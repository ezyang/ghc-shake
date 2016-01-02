{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module GhcShake where

import GhcPlugins hiding ( varName, errorMsg, fatalErrorMsg )
import GHC ( Ghc, setSessionDynFlags, getSession, GhcMonad(..), guessTarget )
import DriverPipeline ( compileFile, preprocess, compileOne', exeFileName, linkBinary )
import DriverPhases ( Phase(..), isHaskellSigFilename )
import PipelineMonad ( PipelineOutput(..) )
import StringBuffer ( hGetStringBuffer )
import HeaderInfo ( getImports )
import Finder ( addHomeModuleToFinder, mkHomeModLocation )
import Platform ( platformBinariesAreStaticLibs )
import LoadIface ( loadSysInterface, loadUserInterface )
import TcRnMonad ( initIfaceCheck )
import FlagChecker ( fingerprintDynFlags )
import TcRnTypes ( mkModDeps )

import Fingerprint
import ErrUtils
import Maybes
import Panic

import GhcShakeInstances
import GhcAction
import Compat
import PersistentCache
import BuildModule

import Development.Shake
import Development.Shake.Classes

-- I'm evil!
import Development.Shake.Core

import Prelude hiding (mod)
import System.Posix.Signals
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import Data.Dynamic
import Data.List
import Data.Tuple
import Control.Monad
import Control.Exception
import System.Environment
import System.FilePath
import System.Exit

frontendPlugin :: FrontendPlugin
frontendPlugin = defaultFrontendPlugin {
        frontend = doShake
    }

-----------------------------------------------------------------------

-- THE BUILD SYSTEM

-----------------------------------------------------------------------

doShake :: [String] -> [(String, Maybe Phase)] -> Ghc ()
doShake args srcs = do
    -- Fix up DynFlags to correct form
    dflags0 <- fmap normaliseDynFlags getDynFlags
    _ <- setSessionDynFlags
        -- HACK: ghc --make -fno-code is not supposed to generate any
        -- interface files, but this is hard to implement in Shake so I
        -- am forcing -fwrite-interface in such cases.
        . flip gopt_set Opt_WriteInterface
        $ oneShotMakeDynFlags dflags0

    -- Get the full DynFlags and HscEnv after fixing DynFlags
    dflags <- getDynFlags
    hsc_env <- getSession

    -- The passed in @srcs@ have three functions:
    --      1. They constitute our top-level 'want's, saying what
    --         we are going to build,
    --      2. They tell us where to find source files, which
    --         may be non-obvious (see 'explicitFileMapping'),
    --      3. They tell us what to link in.
    let (hs_srcs, non_hs_srcs) = partition haskellish srcs
    targets <- mapM (uncurry guessTarget) hs_srcs

    -- Compute the 'ModuleName'/'FilePath' mapping based on file targets
    mod_name_files <- liftIO $ explicitFileMapping hsc_env targets
    -- TODO: error if there's a clobber
    let mod_name_to_file = listToUFM mod_name_files
        file_to_mod_name = Map.fromList (map swap mod_name_files)
        -- TODO this assumes that main module is always thisPackage,
        -- I'm not sure if this is true
        mb_mainFile = lookupUFM mod_name_to_file (moduleName (mainModIs dflags))
        mb_output_file = fmap guessOutputFile mb_mainFile

    -- Also get the object file mapping based on non-Haskell targets
    non_hs_o_files <- liftIO $ getNonHsObjectFiles dflags non_hs_srcs

    -- Setup the correctly guessed outputFile for linking
    let linker_dflags = dflags { outputFile =
            case outputFile dflags0 of
                Nothing -> mb_output_file
                r -> r
            }

    -- TODO: get rid of me?
    -- copypasted from DriverPipeline.hs
    let staticLink = case ghcLink dflags of
                        LinkStaticLib -> True
                        _ -> platformBinariesAreStaticLibs (targetPlatform dflags)
    liftIO $ do

    -- Restore normal signal handlers, since we're not GHCi!
    -- If we don't do this, ^C will not kill us correctly.
    -- TODO: don't try to do this on Windows
    _ <- installHandler sigINT Default Nothing
    _ <- installHandler sigHUP Default Nothing
    _ <- installHandler sigTERM Default Nothing
    _ <- installHandler sigQUIT Default Nothing

    -- Unwrap Shake exceptions so GHC's error handler handles it
    -- properly
    handleGhcErrors $ do

    withArgs args $ do
    let opts = shakeOptions {
            -- If we set -outputdir, we should not be influenced by
            -- build products in the source directory; similarly,
            -- we should have a different Shake instance in this case.
            -- Why not objectDir? Well, you've gotta draw the line
            -- somewhere...
            shakeFiles = case hiDir dflags of
                            Just hidir -> hidir </> ".shake"
                            Nothing -> ".shake",
            shakeThreads = fromMaybe 0 (parMakeCount dflags),
            shakeVersion = "1",
            shakeVerbosity = case verbosity dflags of
                                -- Erm, I think this is right
                                0 -> Quiet
                                1 -> Normal
                                2 -> Normal -- [sic]
                                3 -> Loud
                                4 -> Chatty
                                _ -> Diagnostic,
            -- shakeLint = Just LintBasic, -- for dev
            shakeAssume = if gopt Opt_ForceRecomp dflags
                            then Just AssumeDirty
                            else Nothing,
            shakeExtra = HashMap.fromList [(typeRep (Proxy :: Proxy DynFlags), toDyn dflags)]
        }
    shakeArgs opts $ do

    -- Oracles
    askNonHsObjectFiles <- fmap ($ NonHsObjectFiles ()) . addOracle $
        \(NonHsObjectFiles ()) -> return non_hs_o_files
    askNonHsObjectPhase <- fmap (. NonHsObjectPhase) . addOracle $
        let input_map = Map.fromList (zip non_hs_o_files non_hs_srcs)
        in \(NonHsObjectPhase input_fn) ->
            case Map.lookup input_fn input_map of
                Nothing -> error "askNonHsObjectPhase"
                Just r -> return r
    -- Un-hyphenated identifiers are how to invoke
    _ <- addOracle (askFileModuleName' file_to_mod_name)
    _ <- addOracle (askModuleNameFile' mod_name_to_file)
    _ <- addOracle (lookupModule' dflags)
    -- These are cached because GHC caches them.  I don't mind probing
    -- for this every run but doing a persistent cache lets me avoid
    -- having to plumb these around.
    _ <- addPersistentCache (findHomeModule' dflags)
    _ <- addPersistentCache (findPackageModule' dflags)
    -- This is cached because we want unchanging builds to apply to this
    _ <- addPersistentCache (askRecompKey' hsc_env)

    -- Non-hs files
    want non_hs_o_files
    forM_ non_hs_o_files $
        \output_fn -> do
            output_fn %> \_ -> do
                (input_fn, mb_phase) <- askNonHsObjectPhase output_fn
                need [input_fn]
                output_fn2 <- liftIO $
                    compileFile hsc_env StopLn (input_fn, mb_phase)
                assert (output_fn == output_fn2) $ return ()
                -- TODO: read out dependencies from C compiler

    -- TODO: depend on packagedbs and arguments

    -- Want to build every target a user specified on the command line.
    action $ forP targets $ \target -> case target of
        Target{ targetId = TargetModule mod_name } ->
            needHomeModule mod_name >> return ()
        Target{ targetId = TargetFile file _ } ->
            needFileTarget dflags file >> return ()

    -- Linking is computed separately
    let a_root_isMain = any is_main_target targets
        is_main_target Target{ targetId = TargetModule mod_name }
            = mkModule (thisPackage dflags) mod_name == mainModIs dflags
        is_main_target Target{ targetId = TargetFile file _ }
            = case Map.lookup file file_to_mod_name of
                Nothing -> error "is_main_target"
                Just mod_name -> mkModule (thisPackage dflags) mod_name == mainModIs dflags

    if (not (isNoLink (ghcLink dflags)) && (a_root_isMain || gopt Opt_NoHsMain dflags))
        then want [ exeFileName staticLink linker_dflags ]
        -- Replicated logic in GhcMake
        else when (isJust (outputFile linker_dflags) && ghcLink dflags == LinkBinary) $
                action . liftIO $ do
                    errorMsg dflags $ text
                       ("output was redirected with -o, " ++
                        "but no output will be generated\n" ++
                        "because there is no " ++
                        moduleNameString (moduleName (mainModIs dflags)) ++ " module.")
                    -- ick
                    exitWith (ExitFailure 1)

    -- How to link the top-level thing
    exeFileName staticLink linker_dflags %> \out -> do
        Just main_find <- needMainModule dflags

        -- Compute the transitive home modules
        main_iface <- liftIO . initIfaceCheck hsc_env
                    $ loadSysInterface (text "linking main") (mainModIs dflags)
        let home_deps = map fst -- get the ModuleName
                      . filter (not . snd) -- filter out boot
                      . dep_mods
                      . mi_deps $ main_iface
        home_finds <- mapM needHomeModule home_deps
        let obj_files = map (ml_obj_file . fst) $ catMaybes home_finds
        need =<< askNonHsObjectFiles

        -- duplicated from linkBinary' in DriverPipeline
        -- depend on libraries in the library paths for relink
        let pkg_deps = map fst . dep_pkgs . mi_deps $ main_iface
        pkg_lib_paths <- liftIO $ getPackageLibraryPath dflags pkg_deps
        _libs <- getDirectoryFiles "/" (map (</> "*") pkg_lib_paths)
        -- TODO: properly check this

        -- Reimplements link' in DriverPipeline
        let link = case ghcLink dflags of
                LinkBinary    -> linkBinary
                _             -> error ("don't know how to link this way " ++ show (ghcLink dflags))

        putNormal ("Linking " ++ out ++ " ...")
        quietly . traced "linking" $
            link linker_dflags
                (ml_obj_file (fst main_find) : obj_files) pkg_deps
        return ()

    buildModuleRule $ \bm@(BuildModule raw_file mod is_boot) -> do

        -- This is annoying
        let file = if is_boot then addBootSuffix raw_file else raw_file
        need [file]

        -- TODO: make preprocessing a separate rule.  But how to deal
        -- with dflags modification?  Need to refactor so we get a list
        -- of flags to apply (that's easier to serialize)
        (dflags', hspp_fn) <- liftIO $ preprocess hsc_env (file, Nothing)
        buf <- liftIO $ hGetStringBuffer hspp_fn
        (srcimps, the_imps, L _ mod_name) <- liftIO $ getImports dflags' buf hspp_fn file

        let non_boot_location = buildModuleLocation dflags bm { bm_is_boot = False }
            location = buildModuleLocation dflags bm
        mod' <- liftIO $ addHomeModuleToFinder hsc_env mod_name non_boot_location
        assert (mod == mod') $ return ()

        -- Force the direct dependencies to be compiled.
        unsafeIgnoreDependencies $ do
            mapM_ (needImportedModule False) the_imps
            mapM_ (needImportedModule True) srcimps

        -- Construct the ModSummary
        src_timestamp <- liftIO $ getModificationUTCTime file
        let hsc_src = if isHaskellSigFilename file
                        then HsigFile
                        else if is_boot
                                then HsBootFile
                                else HsSrcFile
            mod_summary = ModSummary {
                        ms_mod = mod,
                        ms_hsc_src = hsc_src,
                        ms_location = location,
                        ms_hspp_file = hspp_fn,
                        ms_hspp_opts = dflags',
                        ms_hspp_buf = Just buf,
                        ms_srcimps = srcimps,
                        ms_textual_imps = the_imps,
                        -- This shouldn't actually be used for anything
                        ms_hs_date = src_timestamp,
                        ms_iface_date = Nothing,
                        ms_obj_date = Nothing
                      }

        -- Build the module
        putNormal ("GHC " ++ file)
        let msg _ _ _ _ = return () -- Be quiet!!
        hmi <- quietly . traced file
              $ compileOne' Nothing (Just msg) hsc_env mod_summary
                            -- We don't know what number the module
                            -- we're building is
                            0 0 Nothing Nothing
                            -- We skip GHC's recompiler checker by
                            -- passing SourceModified because we
                            -- reimplemented it
                            SourceModified

        -- Track fine-grained dependencies
        needInterfaceUsages dflags (hm_iface hmi)

        -- We'd like to add the hmi to the EPS (so we don't attempt
        -- to slurp it in later), but this sometimes deadlocks.  Doesn't
        -- seem to hurt too much if we don't (since the interface
        -- is only loaded once anyways).

    return ()

-----------------------------------------------------------------------

-- THE HELPERS

-----------------------------------------------------------------------

-- | Question type for oracle 'askNonHsObjectFiles'.
newtype NonHsObjectFiles = NonHsObjectFiles ()
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

-- | Question type for oracle 'askNonHsObjectPhase'.
newtype NonHsObjectPhase = NonHsObjectPhase String
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

-- | Remove any "." directory components from paths in 'DynFlags', to
-- help prevent Shake from getting confused (since it doesn't
-- normalise.)
-- TODO: I'm not sure if this helps
normaliseDynFlags :: DynFlags -> DynFlags
normaliseDynFlags dflags =
    dflags {
       hiDir = fmap normalise (hiDir dflags),
       objectDir = fmap normalise (objectDir dflags),
       stubDir = fmap normalise (stubDir dflags),
       outputFile = fmap normalise (outputFile dflags),
       includePaths = map normalise (includePaths dflags),
       importPaths = map normalise (importPaths dflags)
    }

-- | @ghc --make@ puts modules in the HPT but this is annoying
-- to do in Shake, where we don't know the transitive closure
-- of home modules we depend on; demand loading is much
-- more convenient.  The only way to demand load home modules
-- is to be in one-shot mode; this function switches us to
-- 'OneShot' mode, but makes some adjustments to make it simulate
-- @--make@ mode.
oneShotMakeDynFlags :: DynFlags -> DynFlags
oneShotMakeDynFlags dflags =
    dflags { ghcMode = OneShot
             -- As a consequence of being in OneShot mode,
             -- the Finder doesn't search the output hi directory
             -- for interface files.  So this is a gentle hack
             -- to make it search those directories too.
           , importPaths = maybe [] (:[]) (hiDir dflags)
                              ++ importPaths dflags
             -- Another consequence of OneShot mode is that it
             -- will take the setting of outputFile seriously;
             -- however, we only really want that when linking.
             -- So unset outputFile for now.
           , outputFile = Nothing
           }

-- | This function computes an association list between module
-- names and file paths based on any file targets that were passed
-- to GHC explicitly.
--
-- The reason we need to do this is that what file target we specify
-- can influence what hi/o file generates a source file.  For example,
-- suppose we have two files:
--
-- @
--      -- A1.hs
--      module A where
--
--      -- A2.hs
--      module A where
-- @
--
-- If we run @ghc --make A1.hs -outputdir out@, @A1.hs@ is used to buld
-- @out/A.hi@.  But if we say @ghc --make A2.hs -outputdir out@ instead,
-- @A2.hs@ will be used instead!  (GHC will in fact silently clobber
-- files if you specify both at the same time, see
-- https://ghc.haskell.org/trac/ghc/ticket/11201)
--
-- What does this mean for Shake?  First, if we are asked to build some
-- 'ModuleName', to figure out what source file may have generated it,
-- we have to look at the file targets (parsing them to get the
-- module header) to see if any of them define the module in question.
-- Second, we need to make sure that we recompile if the file arguments
-- change in a way that causes the source file we should use to
-- change (normal recompilation checking will NOT catch this!)
--
-- At the moment, we eagerly parse each file target to pull out its
-- module name, and return an association list to handle this.
--
-- TODO: Recompilation checking here is broken.
explicitFileMapping :: HscEnv -> [Target] -> IO [(ModuleName, FilePath)]
explicitFileMapping hsc_env targets = do
    let get_file_target Target { targetId = TargetFile file _ } = Just file
        get_file_target _ = Nothing
        file_targets = mapMaybe get_file_target targets
        dflags = hsc_dflags hsc_env
    forM file_targets $ \file -> do
        -- ahh, it's too bad that we have to redo the preprocessor...
        (dflags', hspp_fn) <- preprocess hsc_env (file, Nothing)
        buf <- hGetStringBuffer hspp_fn
        -- TODO do less work parsing!
        (_, _, L _ mod_name) <- getImports dflags' buf hspp_fn file
        -- Make sure we can find it!
        -- Why do we need this? Try building Setup.hs
        location <- mkHomeModLocation dflags mod_name file
        _ <- addHomeModuleToFinder hsc_env mod_name location
        return (mod_name, file)


-- | If you want to build a @.o@ file, it is ambiguous whether or not it
-- is a Haskell or C file.  For example:
--
-- >    ghc --make A.c A.hs
--
-- will clobber A.o (GHC's build system does no sanity check here.)
-- However, we observe that GHC will never go off and build a
-- non-Haskell source manually; it has to be in non_hs_srcs.  So
-- for EACH non_hs_srcs, we add a rule for how to build its product,
-- with higher priority than the default Haskell rule, and leave
-- it at that.  To do that, we have to precompute the output
-- filenames of each non_hs_src file.
getNonHsObjectFiles :: DynFlags -> [(FilePath, Maybe Phase)]
                    -> IO [FilePath]
getNonHsObjectFiles dflags non_hs_srcs =
    forM non_hs_srcs $ \(input_fn, _) -> do
        -- This code was based off of @compileFile hsc_env StopLn x@
        let -- Technically -fno-code should cause a temporary file to
            -- be made, but making this deterministic is better
            output = Persistent
            (basename, _) = splitExtension input_fn
            stopPhase = StopLn
        getOutputFilename stopPhase output basename dflags stopPhase Nothing

-- | When we raise a 'GhcException' or a 'SourceError', try to give
-- @ghc --make@ compatible output (without the extra Shake wrapping.)
-- This is way better for users, since Shake does not print line numbers
-- for SourceErrors.
handleGhcErrors :: IO a -> IO a
handleGhcErrors m =
    handle (\(e :: ShakeException) ->
                -- TODO: there should be a better way of doing this
                case fromException (shakeExceptionInner e) of
                    Just (e' :: GhcException) -> throwIO e'
                    Nothing -> case fromException (shakeExceptionInner e) of
                        Just (e' :: SourceError) -> throwIO e'
                        Nothing -> throwIO e
                ) m

-- | Depend on a fully qualified Haskell module.
needModule :: DynFlags -> Module -> IsBoot
           -> Action (Maybe (ModLocation, Module))
needModule dflags mod is_boot =
    needFindResult is_boot =<< findExactModule dflags mod

-- | Depend on a module in the home package.
needHomeModule :: ModuleName
               -> Action (Maybe (ModLocation, Module))
needHomeModule mod_name =
    needFindResult False =<< findHomeModule mod_name

-- | Depend on the build products of a file target.
needFileTarget :: DynFlags -> FilePath
               -> Action (Maybe (ModLocation, Module))
needFileTarget dflags file = do
    mod_name <- askFileModuleName file
    let is_boot = "-boot" `isSuffixOf` file
        mod = mkModule (thisPackage dflags) mod_name
        bm = BuildModule file mod is_boot
    needBuildModule bm
    return (Just (buildModuleLocation dflags bm, mod))

-- | Depend on the module pointed by a user import.
needImportedModule :: IsBoot -> (Maybe FastString, Located ModuleName)
                   -> Action (Maybe (ModLocation, Module))
needImportedModule is_boot (mb_pkg, L _ mod_name) = do
    needFindResult is_boot =<< findImportedModule mod_name mb_pkg

-- | Depend on the main module (whatever that is!)
--
-- TODO: Oracle-ize.
needMainModule :: DynFlags -> Action (Maybe (ModLocation, Module))
needMainModule dflags =
    needHomeModule (moduleName (mainModIs dflags))

-- | Helper function to depend on a find result.
needFindResult :: IsBoot -> Maybe (ModLocation, Module) -> Action (Maybe (ModLocation, Module))
needFindResult is_boot r = do
    let maybeAddBootSuffix
            | is_boot   = addBootSuffix
            | otherwise = id
    case r of
        Just (loc, mod) ->
            case ml_hs_file loc of
                Nothing ->
                    need [ maybeAddBootSuffix (ml_hi_file loc) ]
                Just src_file -> do
                    needBuildModule (BuildModule src_file mod is_boot)
        _ -> return () -- Let GHC error when we actually try to look it up
    return r

-- | Depend on the 'RecompKey's as reported by a 'ModIface'.
needInterfaceUsages :: DynFlags -> ModIface -> Action ()
needInterfaceUsages dflags iface = do
    let -- Need this to check if it's boot or not
        mod_deps = mkModDeps (dep_mods (mi_deps iface))
        usageKey UsagePackageModule{ usg_mod = mod }
            = [ ModuleHash mod ]
        usageKey UsageHomeModule{ usg_mod_name = mod_name
                                , usg_entities = entities }
            = ExportHash mod is_boot
            : [ DeclHash mod is_boot occ | (occ, _) <- entities ]
            where mod = mkModule (thisPackage dflags) mod_name
                  is_boot = case lookupUFM mod_deps mod_name of
                                Nothing -> error "bad deps"
                                Just (_, r) -> r
        usageKey UsageFile{}
            = []
        usageFile UsageFile{ usg_file_path = path }
            = [path]
        usageFile _ = []

    -- We could parallelize this but it's kind of pointless
    _ <- askRecompKey (FlagHash (mi_module iface))
    mapM_ askRecompKey (concatMap usageKey (mi_usages iface))
    need (concatMap usageFile (mi_usages iface))

-- | To make Shake's dependency tracking as accurate as possible, we
-- reimplement GHC's recompilation avoidance.  The idea:
--
--      - We express an "orderOnly" constraint on direct
--        interface files to make sure that everything
--        GHC expects to be built is built.
--
--      - We run GHC.
--
--      - We register TRUE dependencies against what GHC
--        recorded it used during compilation (the usage
--        hashes.)
--
-- Shake will only rebuild when these hashes change.
--
-- We need a key for every hash we may want to depend upon, so that
-- Shake can implement fine-grained dependency tracking; that's
-- what 'RecompKey' is for.
askRecompKey :: RecompKey -> Action Fingerprint
askRecompKey = askPersistentCache

-- | Backing implementation for 'askRecompKey'.
askRecompKey' :: HscEnv -> RecompKey -> Action Fingerprint
askRecompKey' hsc_env k = do
    let dflags = hsc_dflags hsc_env
        get_iface mod is_boot = do
            _ <- needModule dflags mod is_boot
            liftIO . initIfaceCheck hsc_env
                   -- not really a user interface load, but it's the
                   -- easiest way to specify boot-edness
                   $ loadUserInterface is_boot (text "export hash") mod
    case k of
        FlagHash mod ->
            liftIO $ fingerprintDynFlags dflags mod putNameLiterally
        ExportHash mod is_boot ->
            fmap mi_exp_hash $ get_iface mod is_boot
        ModuleHash mod ->
            fmap mi_mod_hash $ get_iface mod False
        DeclHash mod is_boot occ -> do
            iface <- get_iface mod is_boot
            return $ case mi_hash_fn iface occ of
                        Nothing -> error "could not find fingerprint"
                        Just (_, fp) -> fp

-- | If there is no -o option, guess the name of target executable
-- by using top-level source file name as a base.
--
-- Pure reimplementation of function in 'GhcMake'.
guessOutputFile :: FilePath -> FilePath
guessOutputFile mainModuleSrcPath =
    let name = dropExtension mainModuleSrcPath
    in if name == mainModuleSrcPath
        then throwGhcException . UsageError $
                 "default output name would overwrite the input file; " ++
                 "must specify -o explicitly"
        else name
