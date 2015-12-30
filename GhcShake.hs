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

import GHC.Generics (Generic)
import System.Posix.Signals
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Typeable
import Data.List
import Data.Maybe
import Data.IORef
import Data.Tuple
import Control.Monad
import Control.Concurrent.MVar
import Control.Exception
import System.Environment
import System.FilePath
import System.Exit
import qualified System.Directory as IO
import qualified Data.IntSet as IntSet

frontendPlugin :: FrontendPlugin
frontendPlugin = defaultFrontendPlugin {
        frontend = doShake
    }

-----------------------------------------------------------------------

-- THE MAIN STUFF

-----------------------------------------------------------------------

doShake :: [String] -> [(String, Maybe Phase)] -> Ghc ()
doShake args srcs = do
    -- These will end up being our top-level wants
    let (hs_srcs, non_hs_srcs) = partition haskellish srcs
    targets <- mapM (uncurry guessTarget) hs_srcs

    dflags00 <- getDynFlags
    -- TODO: I'm not sure if this helps
    let dflags0 = dflags00 {
                   hiDir = fmap normalise (hiDir dflags00),
                   objectDir = fmap normalise (objectDir dflags00),
                   stubDir = fmap normalise (stubDir dflags00),
                   outputFile = fmap normalise (outputFile dflags00),
                   includePaths = map normalise (includePaths dflags00),
                   importPaths = map normalise (importPaths dflags00)
                }
    setSessionDynFlags
        -- Unconditionally turn on -fwrite-interface, otherwise Shake
        -- has no files to generate!
        . flip gopt_set Opt_WriteInterface
        -- ghc --make puts modules in the HPT but this is annoying;
        -- we'd rather demand load as necessary.  So flip to OneShot
        -- mode to make this happen.
        $ dflags0 { ghcMode = OneShot,
                   importPaths = maybe [] (:[]) (fmap normalise (hiDir dflags0))
                                    ++ importPaths dflags0,
                   -- Clear this for normal compilation; we'll
                   -- reenable it when linking
                   outputFile = Nothing
                     }

    dflags <- getDynFlags
    hsc_env <- getSession

    {-
    pprTrace "relevant dflags"
        (vcat [ ppr (mainModIs dflags)
              , ppr (setSafeMode (safeHaskell dflags))
              , ppr (fmap fromEnum (language dflags), IntSet.toList $ extensionFlags dflags)
              , ppr (map normalise (includePaths dflags), opt_P dflags ++ picPOpts dflags)
              , ppr (hcSuf dflags) ]) $ return ()
              -}

    -- File targets are TOTALLY bonkers.  Consider these GHC commands:
    --
    --      ghc --make A.hs -outputdir out
    --      ghc --make A -outputdir out # where A.hs exists
    --
    -- These may output to other places than out/A.hi; the target will
    -- depend on what 'module A' says in the file.  To make matters
    -- worse, even an input that looks like a module name can be guessed
    -- to be a TargetFile, if the file exists, so a client can't even be
    -- sure they managed to force all modules.
    --
    -- Thus, for each file target, we have to eagerly parse them for their
    -- module names, so we know where they're supposed to go.
    let get_file_target Target { targetId = TargetFile file _ } = Just file
        get_file_target _ = Nothing
        file_targets = mapMaybe get_file_target targets
    mod_name_files <- forM file_targets $ \file -> do
        -- ahh, it's too bad that we have to redo the preprocessor...
        (dflags', hspp_fn) <- liftIO $ preprocess hsc_env (file, Nothing)
        buf <- liftIO $ hGetStringBuffer hspp_fn
        -- TODO do less work parsing!
        (_, _, L _ mod_name) <- liftIO $ getImports dflags' buf hspp_fn file
        location <- liftIO $ mkHomeModLocation dflags mod_name file
        _ <- liftIO $ addHomeModuleToFinder hsc_env mod_name location
        return (mod_name, file)
    let mod_name_to_file = listToUFM mod_name_files
        file_to_mod_name = Map.fromList (map swap mod_name_files)
        -- TODO this assumes that main module is always thisPackage,
        -- I'm not sure if this is true
        mb_mainFile = lookupUFM mod_name_to_file (moduleName (mainModIs dflags))
        mb_output_file = fmap guessOutputFile mb_mainFile

    let linker_dflags = dflags { outputFile =
            case outputFile dflags0 of
                Nothing -> mb_output_file
                r -> r
            }
    let -- copypasted from DriverPipeline.hs
        staticLink = case ghcLink dflags of
                        LinkStaticLib -> True
                        _ -> platformBinariesAreStaticLibs (targetPlatform dflags)
    liftIO $ do

    -- TODO: recomp avoidance here is dodgy
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
    non_hs_o_files <- forM non_hs_srcs $ \(input_fn, mb_phase) -> do
        -- This code duplicates compileFile hsc_env StopLn x
        let mb_o_file = outputFile dflags
            -- Some of these cases should be impossible
            output
             -- ToDo: kill this
             | HscNothing <- hscTarget dflags = Temporary
             | not (isNoLink (ghcLink dflags)) = Persistent
             -- ToDo: kill this too
             | isJust mb_o_file = SpecificFile
             | otherwise = Persistent
            (basename, _) = splitExtension input_fn
            stopPhase = StopLn
        output_fn <-
            getOutputFilename stopPhase output basename dflags stopPhase Nothing
        return ((input_fn, mb_phase), output_fn)

    -- Restore normal signal handlers, since we're not GHCi!
    -- TODO: don't try to do this on Windows
    installHandler sigINT Default Nothing
    installHandler sigHUP Default Nothing
    installHandler sigTERM Default Nothing
    installHandler sigQUIT Default Nothing

    statusMsgRef <- newIORef ""

    handle (\(e :: ShakeException) ->
                case fromException (shakeExceptionInner e) of
                    Just (e' :: GhcException) -> throwIO e'
                    Nothing -> case fromException (shakeExceptionInner e) of
                        Just (e' :: SourceError) -> throwIO e'
                        Nothing -> throwIO e
                ) $ do

    withArgs args $ do
    shakeArgs shakeOptions {
        shakeFiles = case hiDir dflags of
                        Just hidir -> hidir </> ".shake"
                        Nothing -> ".shake",
        shakeThreads = fromMaybe 0 (parMakeCount dflags),
        shakeVersion = "1",
        shakeVerbosity = case verbosity dflags of
                            -- Erm, I think this is right
                            0 -> Quiet
                            1 -> Normal
                            2 -> Normal
                            3 -> Loud
                            4 -> Chatty
                            _ -> Diagnostic,
        shakeLint = Just LintBasic, -- for dev
        shakeAssume = if gopt Opt_ForceRecomp dflags
                        then Just AssumeDirty
                        else Nothing,
        shakeProgress = progressDisplay 1 (atomicWriteIORef statusMsgRef)
    } $ do

    -- Non-Haskell files:
    want (map snd non_hs_o_files)
    forM non_hs_o_files $ \((input_fn, mb_phase), output_fn) -> do
        output_fn %> \output_fn2 -> do
            need [input_fn]
            output_fn3 <- liftIO $ compileFile hsc_env StopLn (input_fn, mb_phase)
            assert (output_fn == output_fn2 &&
                    output_fn == output_fn3) $ return ()
            -- TODO: read out dependencies from C compiler

    -- TODO: depend on packagedbs and arguments

    -- Reimplemented FinderCache with dependency tracking.
    find_home    <- newCache (findHomeModule dflags mod_name_to_file)
    find_package <- newCache (findPackageModule dflags)

    -- RecompKey oracle
    addOracle $ \k -> do
        let get_iface mod is_boot = do
                -- TODO: factor this out
                -- Just doing this to get accurate tracking
                r <- findExactModule find_home find_package dflags mod
                case r of
                    Found loc _ -> need [ maybeAddBootSuffix is_boot (ml_hi_file loc) ]
                    _ -> error "couldn't find module for hash lookup"
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

    -- Want to build every target a user specified on the command line.
    action $ forM_ targets $ \target -> case target of
        Target{ targetId = TargetModule mod_name } -> do
            -- No point avoiding probing for the source, because we're
            -- going to need it shortly to build the damn thing
            r <- find_home mod_name
            case r of
                -- TODO: -fno-code, should not request object file
                Found loc _ ->
                    if hscTarget dflags == HscNothing
                        then need [ ml_hi_file loc ]
                        else need [ ml_hi_file loc, ml_obj_file loc ]
                _ -> error ("Could not find module " ++ moduleNameString mod_name)
        Target{ targetId = TargetFile file _ } ->
            case Map.lookup file file_to_mod_name of
                Nothing -> error "should not happen"
                Just mod_name -> do
                    need [ mkHiPath dflags (dropExtension file) (moduleNameSlashes mod_name) ]


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
                     ++ map snd non_hs_o_files -- extra objects
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
    --
    -- This is made further complicated by the fact that -hidir
    -- and -odir are separate. There are a lot of degrees of freedom.
    --      - Actually, this is nearly impossible: the rule needs to
    --      know A PRIORI what file is going to be output.  Which means
    --      we must scan any explicitly specified files at the beginning.
    --
    -- TODO: also pick up C source files here

    let buildHaskell (o:hi:_) = buildHaskell' hi (Just o)
        buildHaskell [hi] = buildHaskell' hi Nothing
        buildHaskell' hi mb_o = do
        let is_boot = "-boot" `isSuffixOf` hi
            maybeAddBootSuffixLocn
                | is_boot   = addBootSuffixLocn
                | otherwise = id
        location <- case hiDir dflags of
            Nothing -> do
                -- The destination path tells us directly where
                -- the source file is
                let basePath = dropExtension hi
                    -- We shouldn't have to probe this again (we
                    -- "found it" before) but it's not obvious
                    -- what the module name we're trying to build
                    -- is.  So this seems to work ok.
                    exts = map (maybeAddBootSuffix is_boot)
                               -- NB: we need to search more here
                               -- because we're not consulting the
                               -- module name to file cache
                               ["hs", "lhs", "hsig", "lhsig", "hspp", "hscpp"]
                    search [] = error "Can't find source file"
                    search (ext:exts) = do
                        b <- doesFileExist (basePath <.> ext)
                        if b then return (basePath <.> ext)
                             else search exts
                path <- search exts
                return ModLocation {
                            ml_hs_file = Just path,
                            ml_hi_file = hi,
                            ml_obj_file = fromMaybe (error "ml_obj_file mb_o") mb_o }
            Just hidir -> do
                -- Determine the ModuleName
                let pathToModuleName prefix path = do
                        let rel = makeRelative prefix path
                            (base, ext) = splitExtension (dropWhile isPathSeparator rel)
                            mod_name = map (\c -> if isPathSeparator c then '.' else c) base
                        guard (looksLikeModuleName mod_name)
                        return (mkModuleName mod_name)

                mod_name <- case pathToModuleName (normalise hidir) hi of
                    Nothing -> error ("Not a module name interface file: " ++ hi)
                    Just mod_name -> return mod_name

                r <- find_home mod_name
                case r of
                    Found loc _ -> return (maybeAddBootSuffixLocn loc)
                    _ -> error ("Could not find source for module " ++ moduleNameString mod_name)

        let file = expectJust "shake hi/o rule" (ml_hs_file location)
            (basename, _) = splitExtension file
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

        _ <- askOracle (FlagHash (mod == mainModIs dflags)) :: Action Fingerprint

        -- Add the direct dependencies
        let find_module (mb_pkg, L _ mod_name) =
                findImportedModule find_home find_package dflags mod_name mb_pkg
        dep_finds <- mapM find_module the_imps
        dep_boot_finds <- mapM find_module srcimps
        let canBuild (Found loc mod) = [ loc ]
            canBuild _ = [] -- could error early here
            hi_deps = map ml_hi_file (concatMap canBuild dep_finds)
            hi_boot_deps = map (ml_hi_file . addBootSuffixLocn)
                               (concatMap canBuild dep_boot_finds)
            o_deps = map ml_obj_file (concatMap canBuild dep_finds)
            o_boot_deps = map (ml_obj_file . addBootSuffixLocn)
                               (concatMap canBuild dep_boot_finds)
        orderOnly (hi_deps ++ hi_boot_deps ++ o_deps ++ o_boot_deps)

        -- deps are all built, now report we're doing it
        -- status_msg <- liftIO $ readIORef statusMsgRef
        -- putNormal ("[" ++ status_msg ++ "] GHC " ++ file)
        putNormal ("GHC " ++ file)

        -- Tricky: where should we get source_unchanged?
        --  - It's unacceptable to say it's always changed, because this
        --    will thwart GHC's recompilation checker.
        --  - You can't replace GHC's recompilation checker with Shake,
        --    because it operates on the level of semantic entities
        --    while Shake works on files. (With a LOT more coordination
        --    you could manage it. That would be an interesting thing
        --    to do.)  To put it another way, Shake's job is to
        --    handle *stability*.
        --  - Possibility 1: directly query the o/hi and hs file for
        --    timestamps and make a determination based on that.
        --  - Possibility 2: get the info out of Shake.  I don't know
        --    how to do this.
        --
        -- So we'll do possibility 1 first.
        --
        -- Careful: Shake's file algorithm is different from stability:
        -- stability is *transitive* in GHC, while Shake is allowed
        -- to not recompile if all of the needs did not change.
        -- We THINK this is equivalent (at least when you're not
        -- using GHCi, anyway), and ghc -M seems to suggest so too;
        -- however, a lint or two would be appreciated.

        -- copy-pasted from DriverPipeline
        let dest_file | writeInterfaceOnlyMode dflags = hi
                      | otherwise                     = fromMaybe (error "dest_file") mb_o

        let msg _ _ _ _ = return () -- Be quiet!!
        hmi <- quietly . traced file
              $ compileOne' Nothing (Just msg) hsc_env mod_summary
                            -- Always report modified! Because we'll
                            -- have skipped the rule if it hadn't.
                            -- Importantly, WE CAN SKIP GHC's
                            -- recompilation checking.
                            0 0 Nothing Nothing SourceModified

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
        forM keys askOracle :: Action [Fingerprint]
        need files

        -- We'd like to add the hmi to the EPS (so we don't attempt
        -- to slurp it in later), but this sometimes deadlocks.  Doesn't
        -- seem to hurt too much if we do.

        -- Don't add when it's boot.  (Could this cause problems?
        -- I don't think so.)
        when (not is_boot) . liftIO $
            addHomeModuleToFinder hsc_env mod_name location >> return ()

        return ()

    -- This ought to be doable with an OR rule
    let wildcard dflags is_boot is_dyn mk =
            maybeAddBootSuffix is_boot
                -- NB: don't use "//*" because then </> will delete
                -- the prefix!
                (mk (maybeMkDynamicDynFlags is_dyn dflags) "**/*" "**/*")

        wildcards dflags is_boot is_dyn =
            map (wildcard dflags is_boot is_dyn) $
                if hscTarget dflags == HscNothing
                    then [mkHiPath]
                    else [mkObjPath, mkHiPath]

    -- TODO: dunno if this conditional is right
    if gopt Opt_BuildDynamicToo dflags
      then
        -- Omnibus rule builds dynamic and not-dynamic simultaneously
        -- NB: non-dynamic first!
        forM_ [False, True] $ \is_boot ->
            concatMap (wildcards dflags is_boot) [False, True]
                &%> buildHaskell
      else
        -- Separate rules for each configuration
        forM_ [False, True] $ \is_boot ->
            -- misnomer: this might be dynamic, it might not
            -- be; they both produce hi/o files
            wildcards dflags is_boot False &%> buildHaskell

    -----------------------------------------------------------------------

    -- RECOMPILATION AVOIDANCE

    -----------------------------------------------------------------------

    -- To make Shake as accurate as possible, we reimplement GHC's
    -- recompilation avoidance.  The general idea is that while we
    -- "need" interface files as a way of telling Shake to go build
    -- it first, but we'll also "need" relevant hashes of interface
    -- files to make Shake rebuild when these hashes change.
    --
    -- We need some way of key'ing the hashes at the granularity we want to
    -- manage recompilation avoidance (we don't want to just grab ALL the
    -- hashes of the interface file because then we'll rebuild too eagerly);
    -- that's what 'RecompKey' is for.  Irritatingly, none of GHC's
    -- built-in types have the instances we need so we have to define
    -- them.
    --
    -- Notably, here are things we don't need to check:
    --
    --      - Imported module not found among previous dependencies.
    --        TODO: Handle queries to the package database elsewhere.
    --
    --      - File hashes: plain old Shake dependencies work great!

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


