{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module GhcShake where

import GhcPlugins hiding ( varName, errorMsg, fatalErrorMsg )
import GHC ( Ghc, setSessionDynFlags, getSession, ImportDecl(..), printException, GhcMonad(..), guessTarget )
import DriverPipeline ( compileFile, preprocess, writeInterfaceOnlyMode, compileOne', compileOne, exeFileName, linkBinary )
import DriverPhases ( Phase(..), isHaskellUserSrcFilename, isHaskellSigFilename
                    , phaseInputExt, eqPhase, isHaskellSrcFilename )
import PipelineMonad ( PipelineOutput(..) )
import SysTools ( newTempName )
import StringBuffer ( hGetStringBuffer )
import HeaderInfo ( getImports )
import PrelNames ( gHC_PRIM, mAIN )
import Finder ( addHomeModuleToFinder, mkHomeModLocation )
import ErrUtils ( printBagOfErrors )
import Platform ( platformBinariesAreStaticLibs )
import LoadIface ( loadSysInterface, loadUserInterface )
import TcRnMonad ( initIfaceCheck )
import Packages ( lookupModuleWithSuggestions )
import FlagChecker ( fingerprintDynFlags )
import TcRnTypes ( mkModDeps )
import qualified Binary as B

import Fingerprint
import ErrUtils
import HscTypes
import InstEnv
import FamInstEnv
import Maybes
import NameEnv
import Panic
import Unique
import OccName
import Module

import GhcShakeInstances
import GhcAction
import Compat

import Development.Shake
import Development.Shake.Rule
import Development.Shake.Classes

-- I'm evil!
import Development.Shake.Rules.File
import Development.Shake.ByteString
import Development.Shake.Core
import General.String

import GHC.Generics (Generic)
import System.Posix.Signals
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import Data.Dynamic
import Data.Bits
import Data.Map (Map)
import Data.Typeable
import Data.List
import Data.Maybe
import Data.IORef
import Data.Tuple
import Data.Either
import Control.Monad
import Control.Concurrent.MVar
import Control.Exception
import System.Environment
import System.FilePath
import System.Exit
import qualified System.Directory as IO
import qualified Data.IntSet as IntSet

newtype NonHsObjectFiles = NonHsObjectFiles ()
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

newtype NonHsObjectPhase = NonHsObjectPhase String
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

frontendPlugin :: FrontendPlugin
frontendPlugin = defaultFrontendPlugin {
        frontend = doShake
    }

-----------------------------------------------------------------------

-- THE MAIN STUFF

-----------------------------------------------------------------------

doShake :: [String] -> [(String, Maybe Phase)] -> Ghc ()
doShake args srcs = do
    -- Fix up DynFlags to correct form
    dflags0 <- fmap normaliseDynFlags getDynFlags
    setSessionDynFlags
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
    installHandler sigINT Default Nothing
    installHandler sigHUP Default Nothing
    installHandler sigTERM Default Nothing
    installHandler sigQUIT Default Nothing

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
            shakeLint = Just LintBasic, -- for dev
            shakeAssume = if gopt Opt_ForceRecomp dflags
                            then Just AssumeDirty
                            else Nothing,
            shakeExtra = HashMap.fromList [(typeRep (Proxy :: Proxy DynFlags), toDyn dflags)]
        }
    shakeArgs opts $ do

    -- Non-Haskell files
    askNonHsObjectFiles <- fmap ($ NonHsObjectFiles ()) . addOracle $
        \(NonHsObjectFiles ()) -> return non_hs_o_files
    askNonHsObjectPhase <- fmap (. NonHsObjectPhase) . addOracle $
        let input_map = Map.fromList (zip non_hs_o_files non_hs_srcs)
        in \(NonHsObjectPhase input_fn) ->
            case Map.lookup input_fn input_map of
                Nothing -> error "askNonHsObjectPhase"
                Just r -> return r

    -- Reimplemented FinderCache with dependency tracking.
    -- TODO: these should be Oracles!
    find_home    <- newCache (findHomeModule dflags mod_name_to_file)
    find_package <- newCache (findPackageModule dflags)

    -- To make Shake as accurate as possible, we reimplement GHC's
    -- recompilation avoidance.  The general idea is that while we
    -- "orderOnly" interface files as a way of telling Shake to go build
    -- it first, but we only "need" the relevant hashes of interface.
    -- Thus, Shake will only rebuild when these hashes change.
    --
    -- We need some way of key'ing the hashes at the granularity we want to
    -- manage recompilation avoidance (we don't want to just grab ALL the
    -- hashes of the interface file because then we'll rebuild too eagerly);
    -- that's what 'RecompKey' is for.
    askRecompKey <- addOracle $ \k -> do
        let get_iface mod is_boot = do
                needModule find_home find_package dflags mod is_boot
                liftIO . initIfaceCheck hsc_env
                       -- BOGUS, but it's the most convenient way
                       -- to pass in boot-edness without mucking
                       -- about with eps_is_boot
                       $ loadUserInterface is_boot (text "export hash") mod
        case k of
            FlagHash b -> do
                r <- liftIO $ fingerprintDynFlags dflags
                    (if b then mainModIs dflags else mkModule (fsToUnitId (fsLit "")) (mkModuleName "")) -- just something that's never equal
                    putNameLiterally
                -- putNormal (show r)
                return r
            ExportHash mod is_boot -> fmap mi_exp_hash $ get_iface mod is_boot
            ModuleHash mod -> fmap mi_mod_hash $ get_iface mod False
            DeclHash mod is_boot occ -> do
                iface <- get_iface mod is_boot
                return $ case mi_hash_fn iface occ of
                            Nothing -> fingerprint0
                            Just (_, fp) -> fp

    want non_hs_o_files
    forM non_hs_o_files $
        \output_fn -> do
            output_fn %> \output_fn -> do
                (input_fn, mb_phase) <- askNonHsObjectPhase output_fn
                need [input_fn]
                output_fn2 <- liftIO $
                    compileFile hsc_env StopLn (input_fn, mb_phase)
                assert (output_fn == output_fn2) $ return ()
                -- TODO: read out dependencies from C compiler

    -- TODO: depend on packagedbs and arguments

    -- Want to build every target a user specified on the command line.
    action $ forP targets $ \target -> case target of
        Target{ targetId = TargetModule mod_name } -> do
            -- No point avoiding probing for the source, because we're
            -- going to need it shortly to build the damn thing
            r <- find_home mod_name
            case r of
                -- TODO: -fno-code, should not request object file
                Found loc mod ->
                    case ml_hs_file loc of
                        Nothing -> need [ ml_hi_file loc ]
                        Just src_file -> do
                            apply1 (BuildModule src_file mod False) :: Action BuildModuleA
                            return ()
                _ -> error ("Could not find module " ++ moduleNameString mod_name)
        Target{ targetId = TargetFile file _ } ->
            case Map.lookup file file_to_mod_name of
                Nothing -> error "should not happen"
                Just mod_name -> do
                    -- TODO: should look at extension to determine
                    -- booted-ness!!
                    apply1 (BuildModule file (mkModule (thisPackage dflags) mod_name) False) :: Action BuildModuleA
                    return ()


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
        -- TODO: this strategy doesn't work for Opt_NoHsMain
        when (gopt Opt_NoHsMain dflags) $ error "-no-hs-main not supported"

        let mainFile = fromJust mb_mainFile
            -- TODO: hack to get linking with dynamic semi-working.
            -- TOdO: use maybeMkDynamicDynFlags
            mkMaybeDynObjPath dflags
                = mkObjPath (maybeMkDynamicDynFlags (gopt Opt_BuildDynamicToo dflags) dflags)
        -- Need both: the object file for linking, the hi file
        -- to figure out what to link
        need [ mkHiPath  dflags (dropExtension mainFile) "Main",
               mkMaybeDynObjPath dflags (dropExtension mainFile) "Main" ]
        -- Compute the transitive home modules
        main_iface <- liftIO . initIfaceCheck hsc_env
                    $ loadSysInterface (text "linking main") mAIN
        let mod_name_deps = map fst . filter (not.snd)
                          . dep_mods . mi_deps $ main_iface
        dep_loc_mods <- getDepLocs find_home mod_name_deps
        -- assert dep_loc_mods is all home modules
        let obj_files = map (ml_obj_file . fst) dep_loc_mods
                     ++ non_hs_o_files -- extra objects
        need obj_files
        let pkg_deps = map fst . dep_pkgs . mi_deps $ main_iface
        -- TODO: this is slightly buggy; if a module is mentioned
        -- on the command line, it should be linked in.
        -- Reimplements link' in DriverPipeline
        let link = case ghcLink dflags of
                LinkBinary    -> linkBinary
                other         -> error ("don't know how to link this way " ++ show (ghcLink dflags))
        -- duplicated from linkBinary' in DriverPipeline
        pkg_lib_paths <- liftIO $ getPackageLibraryPath dflags pkg_deps
        -- depend on libraries in the library paths for relink
        getDirectoryFiles "." (map (</> "*") pkg_lib_paths)
        putNormal ("Linking " ++ out ++ " ...")
        quietly . traced "linking" $
            link linker_dflags
                ((mkMaybeDynObjPath dflags (dropExtension mainFile) "Main")
                    : obj_files) pkg_deps
        return ()

    -- Haskell rules, the plan:
    --  1. From the output file name, find the source file
    --      - If -outputdir is being used, this is done by
    --        reverse engineering the intended ModuleName and then
    --        probing -i for the source file.
    --          - TODO: With a special case for file targets, which
    --            are non -i places where the source file may be.
    --            I don't know how to handle this correctly yet.
    --      - If not, the source file is colocated with the
    --        output file.
    --  2. Parse the source file until you get to dependencies,
    --     and require those
    --  3. Build it!

    rule $ \bm@(BuildModule file mod is_boot) -> Just $ do
        let maybeAddBootSuffixLocn
                | is_boot   = addBootSuffixLocn
                | otherwise = id
            -- TODO duped again!!!
            basename = dropExtension file
            mod_basename = moduleNameSlashes (moduleName mod)
            hi     = mkHiPath      dflags basename mod_basename
            o      = mkObjPath     dflags basename mod_basename
            location = ModLocation {
                            ml_hs_file = Just file,
                            ml_hi_file = hi,
                            ml_obj_file = o
                        }

        let (basename, _) = splitExtension file
            hsc_src = if isHaskellSigFilename file
                        then HsigFile
                        else if is_boot
                                then HsBootFile
                                else HsSrcFile

        need [file]

        -- OK, let's get scrapping.  This is a duplicate of summariseFile.
        -- TODO: make preprocessing a separate rule.  But how to deal
        -- with dflags modification?!
        (dflags', hspp_fn) <- liftIO $ preprocess hsc_env (file, Nothing)
        buf <- liftIO $ hGetStringBuffer hspp_fn
        (srcimps, the_imps, L _ mod_name) <- liftIO $ getImports dflags' buf hspp_fn file
        -- TODO: In 7.10 pretty sure hs location is BOGUS
        -- TODO: Pulling out the source timestamp is hella dodgy
        src_timestamp <- liftIO $ getModificationUTCTime file
        let mod = mkModule (thisPackage dflags) mod_name
            mod_summary = ModSummary {
                        ms_mod = mod,
                        ms_hsc_src = hsc_src,
                        ms_location = location,
                        ms_hspp_file = hspp_fn,
                        ms_hspp_opts = dflags',
                        ms_hspp_buf = Just buf,
                        ms_srcimps = srcimps,
                        ms_textual_imps = the_imps,
                        ms_hs_date = src_timestamp,
                        ms_iface_date = Nothing,
                        ms_obj_date = Nothing
                      }

        askRecompKey (FlagHash (mod == mainModIs dflags))

        -- Add the direct dependencies
        let find_module (mb_pkg, L _ mod_name) =
                findImportedModule find_home find_package dflags mod_name mb_pkg
        dep_finds <- mapM find_module the_imps
        dep_boot_finds <- mapM find_module srcimps
        let canBuild is_boot (Found loc mod) =
                case ml_hs_file loc of
                    Nothing -> [Left (ml_hi_file loc)]
                    Just hs -> [Right (BuildModule hs mod is_boot)]
            canBuild _ _ = [] -- could error early here
            deps = concatMap (canBuild False) dep_finds
            boot_deps = concatMap (canBuild True) dep_boot_finds
            (external_deps, home_deps) = partitionEithers (deps ++ boot_deps)
        need external_deps
        _ <- unsafeIgnoreDependencies $ (apply home_deps :: Action [BuildModuleA])

        -- Deps are all built, now report we're building this module
        putNormal ("GHC " ++ file)

        -- copy-pasted from DriverPipeline
        let dest_file | writeInterfaceOnlyMode dflags = hi
                      | otherwise                     = o

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

        -- Register fine-grained dependencies
        let iface = hm_iface hmi
            -- Need this to check if it's boot or not
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
            keys = concatMap usageKey (mi_usages iface)
            files = concatMap usageFile (mi_usages iface)
        -- We could parallelize this but it's kind of pointless
        mapM askRecompKey keys
        need files

        -- We'd like to add the hmi to the EPS (so we don't attempt
        -- to slurp it in later), but this sometimes deadlocks.  Doesn't
        -- seem to hurt too much if we do.

        -- Don't add when it's boot.  (Could this cause problems?
        -- I don't think so.)
        when (not is_boot) . liftIO $
            addHomeModuleToFinder hsc_env mod_name location >> return ()

        -- OK, compute the up-to-date BuildModuleA
        -- The idea is that if we recompiled, this invalidates ANY build
        -- products we didn't actually build
        r <- liftIO $ storedValue opts bm
        let coverUpObj | hscTarget dflags == HscNothing = \bma -> bma { bma_o = Nothing }
                       | otherwise = id
            coverUpDyn | gopt Opt_BuildDynamicToo dflags = id
                       | otherwise = \bma -> bma { bma_dyn_hi = Nothing, bma_dyn_o = Nothing }
        case r of
            Nothing -> error "eek!"
            Just ans -> return (coverUpDyn (coverUpObj ans))

    return ()

putNameLiterally :: B.BinHandle -> Name -> IO ()
putNameLiterally bh name =
  do
    B.put_ bh $! nameModule name
    B.put_ bh $! nameOccName name

maybeAddBootSuffix is_boot
    | is_boot   = addBootSuffix
    | otherwise = id

maybeMkDynamicDynFlags is_dyn
    | is_dyn = dynamicTooMkDynamicDynFlags
    | otherwise = id

-----------------------------------------------------------------------

-- THE HELPER

-----------------------------------------------------------------------

-- Remove any "." directory components from paths in 'DynFlags', to
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
    let dflags = hsc_dflags hsc_env
        get_file_target Target { targetId = TargetFile file _ } = Just file
        get_file_target _ = Nothing
        file_targets = mapMaybe get_file_target targets
    forM file_targets $ \file -> do
        -- ahh, it's too bad that we have to redo the preprocessor...
        (dflags', hspp_fn) <- preprocess hsc_env (file, Nothing)
        buf <- hGetStringBuffer hspp_fn
        -- TODO do less work parsing!
        (_, _, L _ mod_name) <- getImports dflags' buf hspp_fn file
        location <- mkHomeModLocation dflags mod_name file
        _ <- addHomeModuleToFinder hsc_env mod_name location
        return (mod_name, file)


-- If you want to build a .o file, it is ambiguous whether or not it
-- is a Haskell or C file.  For example:
--
--      ghc --make A.c A.hs
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
    forM non_hs_srcs $ \(input_fn, mb_phase) -> do
        -- This code was based off of @compileFile hsc_env StopLn x@
        let -- Technically -fno-code should cause a temporary file to
            -- be made, but making this deterministic is better
            output = Persistent
            (basename, _) = splitExtension input_fn
            stopPhase = StopLn
        getOutputFilename stopPhase output basename dflags stopPhase Nothing

handleGhcErrors :: IO a -> IO a
handleGhcErrors m =
    -- When we run into a GhcException or a SourceError, try to give
    -- ghc --make compatible output (without the extra Shake wrapping.)
    -- In fact, we MUST do this because Shake does not print
    -- line-numbers for SourceErrors.
    handle (\(e :: ShakeException) ->
                -- TODO: there should be a better way of doing this
                case fromException (shakeExceptionInner e) of
                    Just (e' :: GhcException) -> throwIO e'
                    Nothing -> case fromException (shakeExceptionInner e) of
                        Just (e' :: SourceError) -> throwIO e'
                        Nothing -> throwIO e
                ) m

-- TODO: get rid of me
getDepLocs :: (ModuleName -> Action FindResult) -> [ModuleName]
           -> Action [(ModLocation, Module)]
getDepLocs finder home_mods = do
    rs <- mapM finder home_mods
    -- NB: We only need hi files to build, not o files!
    -- TODo: This is not complete; we also have to track the
    -- individual usages.  GHC will give us this information.
    let canBuild (Found loc mod) = [ (loc, mod) ]
        -- NB: don't error here, might be an external package import
        canBuild _ = []
    return $ concatMap canBuild rs

-- The goods

data BuildModuleA = BuildModuleA
    { bma_hi     :: Maybe FileA
    , bma_o      :: Maybe FileA
    , bma_dyn_hi :: Maybe FileA
    , bma_dyn_o  :: Maybe FileA
    }
    deriving (Eq, Generic, Typeable, Show)
instance Binary BuildModuleA
instance NFData BuildModuleA
instance Hashable BuildModuleA

shakeDynFlags :: ShakeOptions -> DynFlags
shakeDynFlags opts =
    case HashMap.lookup (typeRep (Proxy :: Proxy DynFlags)) (shakeExtra opts) of
        Nothing -> error "no DynFlags"
        Just d -> case fromDynamic d of
                    Just dflags -> dflags
                    Nothing -> error "bad type"

-- This is similar to the Files rule, but it is a bit more relaxed
-- about what should happen if things are missing depending on
-- the presence of the @-dynamic-too@ flag.
instance Rule BuildModule BuildModuleA where
    -- TODO src_filename here is WRONG
    storedValue opts (BuildModule src_filename mod is_boot) = do
        -- Need the DynFlags to compute the paths
        let dflags = shakeDynFlags opts
            basename = dropExtension src_filename
            mod_basename = moduleNameSlashes (moduleName mod)
            dyn_dflags = dynamicTooMkDynamicDynFlags dflags
            hi     = mkHiPath      dflags basename mod_basename
            o      = mkObjPath     dflags basename mod_basename
            dyn_hi = mkHiPath  dyn_dflags basename mod_basename
            dyn_o  = mkObjPath dyn_dflags basename mod_basename
            mkFileQ = FileQ . packU_ . filepathNormalise . unpackU_ . packU
        mb_hi       <- storedValue opts (mkFileQ hi)
        mb_o        <- storedValue opts (mkFileQ o)
        mb_dyn_hi   <- storedValue opts (mkFileQ dyn_hi)
        mb_dyn_o    <- storedValue opts (mkFileQ dyn_o)
        return (Just (BuildModuleA mb_hi mb_o mb_dyn_hi mb_dyn_o))
    equalValue opts (BuildModule src_filename mod is_boot) v1 v2 =
        -- TODO dedupe
        let dflags = shakeDynFlags opts
            basename = dropExtension src_filename
            mod_basename = moduleNameSlashes (moduleName mod)
            dyn_dflags = dynamicTooMkDynamicDynFlags dflags
            hi     = mkHiPath      dflags basename mod_basename
            o      = mkObjPath     dflags basename mod_basename
            dyn_hi = mkHiPath  dyn_dflags basename mod_basename
            dyn_o  = mkObjPath dyn_dflags basename mod_basename
            mkFileQ = FileQ . packU_ . filepathNormalise . unpackU_ . packU
        in foldr and_ EqualCheap
            $ [ test (mkFileQ hi) bma_hi ]
           ++ if hscTarget dflags == HscNothing
                then []
                else [ test (mkFileQ o) bma_o ]
                  ++ if gopt Opt_BuildDynamicToo dflags
                        then [ test (mkFileQ dyn_hi) bma_dyn_hi
                             , test (mkFileQ dyn_o) bma_dyn_o ]
                        else []
      where test k sel = case equalValue opts k <$> sel v1 <*> sel v2 of
                            Nothing -> NotEqual
                            Just r -> r
            and_ NotEqual x = NotEqual
            and_ EqualCheap x = x
            and_ EqualExpensive x = if x == NotEqual then NotEqual else EqualExpensive

needModule :: (ModuleName -> Action FindResult)
           -> (Module -> Action FindResult)
           -> DynFlags -> Module -> IsBoot -> Action ()
needModule find_home find_package dflags mod is_boot = do
    r <- findExactModule find_home find_package dflags mod
    case r of
        Found loc mod ->
            case ml_hs_file loc of
                Nothing -> need [ maybeAddBootSuffix is_boot (ml_hi_file loc) ]
                Just src_file -> do
                    apply1 (BuildModule src_file mod is_boot) :: Action BuildModuleA
                    return ()
        _ -> error "couldn't find module for hash lookup"
