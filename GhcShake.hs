{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module GhcShake where

import GhcPlugins
import GHC ( Ghc, setSessionDynFlags, getSession, ImportDecl(..), printException, GhcMonad(..) )
import DriverPipeline ( compileFile, preprocess, writeInterfaceOnlyMode, compileOne', compileOne, exeFileName, linkBinary )
import DriverPhases ( Phase(..), isHaskellUserSrcFilename, isHaskellSigFilename
                    , phaseInputExt, eqPhase, isHaskellSrcFilename )
import PipelineMonad ( PipelineOutput(..) )
import SysTools ( newTempName )
import StringBuffer ( hGetStringBuffer )
import HeaderInfo ( getImports )
import PrelNames ( gHC_PRIM, mAIN )
import HscMain ( hscCompileOneShot )
import Finder ( addHomeModuleToFinder, mkHomeModLocation )
import ErrUtils ( printBagOfErrors )
import Platform ( platformBinariesAreStaticLibs )
import LoadIface ( loadSysInterface )
import TcRnMonad ( initIfaceCheck )

import HscTypes
import InstEnv
import FamInstEnv
import Maybes
import NameEnv
import Panic

import Development.Shake
import Development.Shake.Rule
import Development.Shake.Classes

import System.Posix.Signals
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Typeable
import Data.List
import Data.Maybe
import Data.IORef
import Control.Monad
import Control.Concurrent.MVar
import Control.Exception
import System.Environment
import System.FilePath
import System.Exit
import qualified System.Directory as IO

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

    -- For now, we assume that a file target is the executable target.
    let get_file_target Target { targetId = TargetFile file _ } = Just file
        get_file_target _ = Nothing
        mb_mainFile
          = case mapMaybe get_file_target targets of
                [] -> Nothing
                [x] -> Just x
                (_:_:_) -> error "Multiple file targets not supported"
        mb_output_file = fmap guessOutputFile mb_mainFile

    dflags0 <- getDynFlags
    setSessionDynFlags
        -- ghc --make puts modules in the HPT but this is annoying;
        -- we'd rather demand load as necessary.  So flip to OneShot
        -- mode to make this happen.  Food for thought: WHY can't
        -- we just get rid of the HPT?  One downside: less obvious
        -- how to do linking.  We'll cross that bridge eventually.
        (dflags0 { ghcMode = OneShot, -- IRRITATING
                   -- DANGER, this is OK because default is LinkBinary
                   -- ghcLink = LinkBinary,
                   importPaths = maybe [] (:[]) (hiDir dflags0) ++ importPaths dflags0,
                   -- clear it for normal compilation
                   outputFile = Nothing
                     })

    dflags <- getDynFlags
    let linker_dflags = dflags { outputFile =
            case outputFile dflags0 of
                Nothing -> mb_output_file
                r -> r
            }
    let -- copypasted from DriverPipeline.hs
        staticLink = case ghcLink dflags of
                        LinkStaticLib -> True
                        _ -> platformBinariesAreStaticLibs (targetPlatform dflags)

    hsc_env <- getSession
    liftIO $ do

    -- Restore normal signal handlers, since we're not GHCi!
    -- TODO: don't try to do this on Windows
    installHandler sigINT Default Nothing
    installHandler sigHUP Default Nothing
    installHandler sigTERM Default Nothing
    installHandler sigQUIT Default Nothing

    statusMsgRef <- newIORef ""

    withArgs args $ do
    shakeArgs shakeOptions {
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

    when (mainModIs dflags /= mAIN) $
        error "-main-is not supported"

    when (not (null non_hs_srcs)) $ error "non-Haskell source files not supported"

    -- Reimplemented FinderCache with dependency tracking.
    finder <- newCache (findHomeModule dflags mb_mainFile)

    -- Want to build every target a user specified on the command line.
    action $ forM_ targets $ \target -> case target of
        Target{ targetId = TargetModule mod_name } -> do
            -- No point avoiding probing for the source, because we're
            -- going to need it shortly to build the damn thing
            let mod_name_str = moduleNameString mod_name
            r <- finder mod_name_str
            case r of
                -- TODO: -fno-code, should not request object file
                Found loc _ -> need [ ml_hi_file loc, ml_obj_file loc ]
                _ -> error ("Could not find module " ++ mod_name_str)
        Target{ targetId = TargetFile file _ } ->
            -- Supporting this in full generality is difficult
            --      * We assume this is for an executable, so only
            --        one file target is supported.
            --      * We assume -main-is is NOT set (so the module
            --        defines Main)
            if isNoLink (ghcLink dflags)
                then need [ mkHiPath dflags (dropExtension file) "Main" ]
                else need [ exeFileName staticLink linker_dflags ]

    -- How to link the top-level thing
    exeFileName staticLink linker_dflags %> \out -> do
        let mainFile = fromJust mb_mainFile
        need [ mkHiPath dflags (dropExtension mainFile) "Main" ]
        -- Compute the transitive home modules
        main_iface <- liftIO . initIfaceCheck hsc_env
                    $ loadSysInterface (text "linking main") mAIN
        let mod_name_deps = map fst . filter (not.snd)
                          . dep_mods . mi_deps $ main_iface
        dep_loc_mods <- getDepLocs finder mod_name_deps
        -- assert dep_loc_mods is all home modules
        let obj_files = map (ml_obj_file . fst) dep_loc_mods
        need obj_files
        let pkg_deps = map fst . dep_pkgs . mi_deps $ main_iface
        -- TODO: this is slightly buggy; if a module is mentioned
        -- on the command line, it should be linked in.
        -- Reimplements link' in DriverPipeline
        let link = case ghcLink dflags of
                LinkBinary    -> linkBinary
                other         -> error "don't know how to link this way"
        traced "linking" $
            link linker_dflags
                ((mkObjPath dflags (dropExtension mainFile) "Main")
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

    [mkObjPath dflags "//*" "//*",
     mkHiPath  dflags "//*" "//*"] &%> \[o, hi] -> do
        location <- case hiDir dflags of
            Nothing -> do
                -- The destination path tells us directly where
                -- the source file is
                let basePath = dropExtension hi
                    -- We shouldn't have to probe this again (we
                    -- "found it" before) but it's not obvious
                    -- what the module name we're trying to build
                    -- is.  So this seems to work ok.
                    exts = ["hs", "lhs", "hsig", "lhsig"]
                    search [] = error "Can't find file"
                    search (ext:exts) = do
                        b <- doesFileExist (basePath <.> ext)
                        if b then return (basePath <.> ext)
                             else search exts
                path <- search exts
                return ModLocation {
                            ml_hs_file = Just path,
                            ml_hi_file = hi,
                            ml_obj_file = o }
            Just hidir -> do
                -- Determine the ModuleName
                let pathToModuleName prefix path = do
                        path <- stripPrefix prefix path
                        path <- stripPrefix "/" path `mplus` return path
                        let (base, ext) = splitExtension (dropWhile isPathSeparator path)
                            mod_name = map (\c -> if isPathSeparator c then '.' else c) base
                        guard (looksLikeModuleName mod_name)
                        return mod_name

                mod_name <- case pathToModuleName hidir hi of
                    Nothing -> error ("Not a module name interface file: " ++ hi)
                    Just mod_name -> return mod_name

                r <- finder mod_name
                case r of
                    Found loc _ -> return loc
                    _ -> error ("Could not find source for module " ++ mod_name)

        let file = expectJust "shake hi/o rule" (ml_hs_file location)
            (basename, _) = splitExtension file
            hsc_src = if isHaskellSigFilename file then HsigFile else HsSrcFile

        need [file]

        status_msg <- liftIO $ readIORef statusMsgRef
        putNormal ("[" ++ status_msg ++ "] GHC " ++ file)

        -- OK, let's get scrapping.  This is a duplicate of summariseFile.
        -- TODO: make preprocessing a separate rule.  But how to deal
        -- with dflags modification?!
        (dflags', hspp_fn) <- liftIO $ preprocess hsc_env (file, Nothing)
        buf <- liftIO $ hGetStringBuffer hspp_fn
        (srcimps, the_imps, L _ mod_name) <- liftIO $ getImports dflags' buf hspp_fn file
        -- TODO: In 7.10 pretty sure hs location is BOGUS
        -- TODO: addHomeModuleToFinder?! Hella dodgy.  This has to be run EVERY
        -- build.
        -- Hella dodgy
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

        -- Add the dependencies
        -- TODO refactor this with target
        let home_mod_names = map unLoc (ms_home_imps mod_summary)
        dep_loc_mods <- getDepLocs finder home_mod_names
        need (map (ml_hi_file . fst) dep_loc_mods)
        -- TODO hs-boot

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
                      | otherwise                     = o
        source_unchanged <- liftIO $
                     -- DO NOT use Shake's version; that would be a
                     -- circular dependency.
                  do dest_file_exists <- IO.doesFileExist dest_file
                     if not dest_file_exists
                        then return SourceModified       -- Need to recompile
                        else do t2 <- getModificationUTCTime dest_file
                                if t2 > src_timestamp
                                  then return SourceUnmodified
                                  else return SourceModified

        let msg _ _ _ _ = return () -- Be quiet!!
        hmi <- quietly . traced file
              -- Shake destroyed our exception handler boo hoo
              . handle (\(e :: SourceError) -> printBagOfErrors dflags (srcErrorMessages e)
                                            >> error "compileOne'")
              $ compileOne' Nothing (Just msg) hsc_env mod_summary
                            0 0 Nothing Nothing source_unchanged

        -- We'd like to add the hmi to the EPS, but this sometimes
        -- deadlocks.
        liftIO $ addHomeModuleToFinder hsc_env mod_name location

        return ()

    return ()


{-
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

    -- Non-Haskell files:
    want (map snd non_hs_o_files)
    forM non_hs_o_files $ \((input_fn, mb_phase), output_fn) -> do
        output_fn %> \output_fn2 -> do
            need [input_fn]
            output_fn3 <- liftIO $ compileFile hsc_env StopLn (input_fn, mb_phase)
            -- TODO: assert all output_fns are the same
            assert (output_fn == output_fn2 &&
                    output_fn == output_fn3) $ return ()
            -- TODO: read out dependencies from C compiler
-}

-----------------------------------------------------------------------

-- THE HELPER

-----------------------------------------------------------------------

getDepLocs :: (String -> Action FindResult) -> [ModuleName]
           -> Action [(ModLocation, Module)]
getDepLocs finder home_mods = do
    rs <- mapM (finder . moduleNameString) home_mods
    -- NB: We only need hi files to build, not o files!
    -- TODo: This is not complete; we also have to track the
    -- individual usages.  GHC will give us this information.
    let canBuild (Found loc mod) = [ (loc, mod) ]
        -- NB: don't error here, might be an external package import
        canBuild _ = []
    return $ concatMap canBuild rs

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

-----------------------------------------------------------------------

-- THE REIMPLEMENTED

-----------------------------------------------------------------------

-- A lot of behavior (e.g. how a .o file is to be made) depends on
-- our ability to actually find the relevant Haskell source file.
-- In GHC, the "Finder" is responsible for implementing this logic.
--
-- However, finder actions are *build-system* relevant.  So we have
-- to reimplement them here so that they are properly tracked.

-- NB: mb_mainFile is to tell where to find the Main file.  In general,
-- ALL file targets could contribute extra found modules, but we're
-- only supporting main for now.
findHomeModule :: DynFlags -> Maybe FilePath -> (String -> Action FindResult)
findHomeModule dflags mb_mainFile str_mod_name =
   let
     mod_name = mkModuleName str_mod_name
     home_path = importPaths dflags
     hisuf = hiSuf dflags
     mod = mkModule (thisPackage dflags) mod_name

     exts =
      [ ("hs",   mkHomeModLocationSearched dflags mod_name "hs")
      , ("lhs",  mkHomeModLocationSearched dflags mod_name "lhs")
      , ("hsig",  mkHomeModLocationSearched dflags mod_name "hsig")
      , ("lhsig",  mkHomeModLocationSearched dflags mod_name "lhsig")
      ]

   in
  if mod == gHC_PRIM
    then return (Found (error "GHC.Prim ModLocation") mod)
    else case mb_mainFile of
            Just mainFile
                | str_mod_name == "Main" -> do
                loc <- liftIO $ mkHomeModLocation dflags (moduleName mAIN) mainFile
                return (Found loc mAIN)
            _ -> searchPathExts home_path mod exts

type FileExt = String
type BaseName = String

mkHomeModLocationSearched :: DynFlags -> ModuleName -> FileExt
                          -> FilePath -> BaseName -> ModLocation
mkHomeModLocationSearched dflags mod suff path basename =
   mkHomeModLocation2 dflags mod (if path == "." then basename
                                                 else path </> basename) suff

mkHomeModLocation2 :: DynFlags
                   -> ModuleName
                   -> FilePath  -- Of source module, without suffix
                   -> String    -- Suffix
                   -> ModLocation
mkHomeModLocation2 dflags mod src_basename ext =
   let mod_basename = moduleNameSlashes mod

       obj_fn = mkObjPath  dflags src_basename mod_basename
       hi_fn  = mkHiPath   dflags src_basename mod_basename

   in (ModLocation{ ml_hs_file   = Just (src_basename <.> ext),
                    ml_hi_file   = hi_fn,
                    ml_obj_file  = obj_fn })

searchPathExts
  :: [FilePath]         -- paths to search
  -> Module             -- module name
  -> [ (
        FileExt,                             -- suffix
        FilePath -> BaseName -> ModLocation  -- action
       )
     ]
  -> Action FindResult

searchPathExts paths mod exts
   = do result <- search to_search
        return result

  where
    basename = moduleNameSlashes (moduleName mod)

    to_search :: [(FilePath, ModLocation)]
    to_search = [ (file, fn path basename)
                | path <- paths,
                  (ext,fn) <- exts,
                  let base | path == "." = basename
                           | otherwise   = path </> basename
                      file = base <.> ext
                ]

    search [] = return (NotFound { fr_paths = map fst to_search
                                 , fr_pkg   = Just (modulePackageKey mod)
                                 , fr_mods_hidden = [], fr_pkgs_hidden = []
                                 , fr_suggestions = [] })

    search ((file, loc) : rest) = do
      b <- doesFileExist file
      if b
        then return (Found loc mod)
        else search rest

-- Reimplemented this because the default algo treats too many things
-- as files
guessTarget :: GhcMonad m => String -> Maybe Phase -> m Target
guessTarget str (Just phase)
   = return (Target (TargetFile str (Just phase)) True Nothing)
guessTarget str Nothing
   | isHaskellSrcFilename file
   = return (target (TargetFile file Nothing))
   | otherwise
   = do if looksLikeModuleName file
           then return (target (TargetModule (mkModuleName file)))
           else do
        dflags <- getDynFlags
        liftIO $ throwGhcExceptionIO
                 (ProgramError (showSDoc dflags $
                 text "target" <+> quotes (text file) <+> 
                 text "is not a module name or a source file"))
     where
         (file,obj_allowed)
                | '*':rest <- str = (rest, False)
                | otherwise       = (str,  True)

         target tid = Target tid obj_allowed Nothing

-----------------------------------------------------------------------

-- COPYPASTA

-----------------------------------------------------------------------


-- copypasted from ghc/Main.hs
-- TODO: put this in a library
haskellish (f,Nothing) =
  looksLikeModuleName f || isHaskellUserSrcFilename f || '.' `notElem` f
haskellish (_,Just phase) =
  phase `notElem` [ As True, As False, Cc, Cobjc, Cobjcpp, CmmCpp, Cmm
                  , StopLn]

-- getOutputFilename copypasted from DriverPipeline
-- ToDo: uncopypaste
-- Notice that StopLn output is always .o! Very useful.
getOutputFilename
  :: Phase -> PipelineOutput -> String
  -> DynFlags -> Phase{-next phase-} -> Maybe ModLocation -> IO FilePath
getOutputFilename stop_phase output basename dflags next_phase maybe_location
 | is_last_phase, Persistent   <- output = persistent_fn
 | is_last_phase, SpecificFile <- output = case outputFile dflags of
                                           Just f -> return f
                                           Nothing ->
                                               panic "SpecificFile: No filename"
 | keep_this_output                      = persistent_fn
 | otherwise                             = newTempName dflags suffix
    where
          hcsuf      = hcSuf dflags
          odir       = objectDir dflags
          osuf       = objectSuf dflags
          keep_hc    = gopt Opt_KeepHcFiles dflags
          keep_s     = gopt Opt_KeepSFiles dflags
          keep_bc    = gopt Opt_KeepLlvmFiles dflags

          myPhaseInputExt HCc       = hcsuf
          myPhaseInputExt MergeStub = osuf
          myPhaseInputExt StopLn    = osuf
          myPhaseInputExt other     = phaseInputExt other

          is_last_phase = next_phase `eqPhase` stop_phase

          -- sometimes, we keep output from intermediate stages
          keep_this_output =
               case next_phase of
                       As _    | keep_s     -> True
                       LlvmOpt | keep_bc    -> True
                       HCc     | keep_hc    -> True
                       _other               -> False

          suffix = myPhaseInputExt next_phase

          -- persistent object files get put in odir
          persistent_fn
             | StopLn <- next_phase = return odir_persistent
             | otherwise            = return persistent

          persistent = basename <.> suffix

          odir_persistent
             | Just loc <- maybe_location = ml_obj_file loc
             | Just d <- odir = d </> persistent
             | otherwise      = persistent

-- Copypaste from Finder

-- | Constructs the filename of a .o file for a given source file.
-- Does /not/ check whether the .o file exists
mkObjPath
  :: DynFlags
  -> FilePath           -- the filename of the source file, minus the extension
  -> String             -- the module name with dots replaced by slashes
  -> FilePath
mkObjPath dflags basename mod_basename = obj_basename <.> osuf
  where
                odir = objectDir dflags
                osuf = objectSuf dflags

                obj_basename | Just dir <- odir = dir </> mod_basename
                             | otherwise        = basename


-- | Constructs the filename of a .hi file for a given source file.
-- Does /not/ check whether the .hi file exists
mkHiPath
  :: DynFlags
  -> FilePath           -- the filename of the source file, minus the extension
  -> String             -- the module name with dots replaced by slashes
  -> FilePath
mkHiPath dflags basename mod_basename = hi_basename <.> hisuf
 where
                hidir = hiDir dflags
                hisuf = hiSuf dflags

                hi_basename | Just dir <- hidir = dir </> mod_basename
                            | otherwise         = basename

-- Copypasted from GhcMake
home_imps :: [Located (ImportDecl RdrName)] -> [Located ModuleName]
home_imps imps = [ ideclName i |  L _ i <- imps, isLocal (ideclPkgQual i) ]
  where isLocal Nothing = True
        isLocal (Just pkg) | pkg == fsLit "this" = True -- "this" is special
        isLocal _ = False

ms_home_allimps :: ModSummary -> [ModuleName]
ms_home_allimps ms = map unLoc (ms_home_srcimps ms ++ ms_home_imps ms)

ms_home_srcimps :: ModSummary -> [Located ModuleName]
ms_home_srcimps = home_imps . ms_srcimps

ms_home_imps :: ModSummary -> [Located ModuleName]
ms_home_imps = home_imps . ms_imps

-- | If there is no -o option, guess the name of target executable
-- by using top-level source file name as a base.
guessOutputFile :: FilePath -> FilePath
guessOutputFile mainModuleSrcPath =
    let name = dropExtension mainModuleSrcPath
    in if name == mainModuleSrcPath
        then throwGhcException . UsageError $
                 "default output name would overwrite the input file; " ++
                 "must specify -o explicitly"
        else name
