{-# LANGUAGE NondecreasingIndentation #-}
module GhcAction where

import GhcPlugins hiding ( varName )
import GHC ( Ghc, setSessionDynFlags, getSession, ImportDecl(..), printException, GhcMonad(..) )
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
import LoadIface ( loadSysInterface )
import TcRnMonad ( initIfaceCheck )
import Packages ( lookupModuleWithSuggestions )
import FlagChecker ( fingerprintDynFlags )

import Fingerprint
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
import Control.Monad
import Control.Concurrent.MVar
import Control.Exception
import System.Environment
import System.FilePath
import System.Exit
import qualified System.Directory as IO

-----------------------------------------------------------------------

-- THE REIMPLEMENTED

-----------------------------------------------------------------------

-- A lot of behavior (e.g. how a .o file is to be made) depends on
-- our ability to actually find the relevant Haskell source file.
-- In GHC, the "Finder" is responsible for implementing this logic.
--
-- However, finder actions are *build-system* relevant.  So we have
-- to reimplement them here so that they are properly tracked.

findImportedModule ::
       (ModuleName -> Action FindResult) -- findHomeModule
    -> (Module -> Action FindResult)      -- findPackageModule
    -> DynFlags -> ModuleName -> Maybe FastString -> Action FindResult
findImportedModule find_home find_package dflags mod_name mb_pkg =
  case mb_pkg of
        Nothing                        -> unqual_import
        Just pkg | pkg == fsLit "this" -> home_import -- "this" is special
                 | otherwise           -> pkg_import
  where
    home_import   = find_home mod_name

    pkg_import    = findExposedPackageModule find_package dflags mod_name mb_pkg

    unqual_import = home_import
                    `orIfNotFound`
                    findExposedPackageModule find_package dflags mod_name Nothing

findExactModule :: (ModuleName -> Action FindResult)
                -> (Module -> Action FindResult)
                -> DynFlags -> Module -> Action FindResult
findExactModule find_home find_package dflags mod =
    if moduleUnitId mod == thisPackage dflags
       then find_home (moduleName mod)
       else find_package mod

findExposedPackageModule :: (Module -> Action FindResult)
                         -> DynFlags -> ModuleName -> Maybe FastString
                         -> Action FindResult
findExposedPackageModule find_package dflags mod_name mb_pkg
  = findLookupResult find_package
  $ lookupModuleWithSuggestions
        dflags mod_name mb_pkg

findLookupResult :: (Module -> Action FindResult)
                 -> LookupResult -> Action FindResult
findLookupResult find_package r = case r of
     LookupFound m _ -> -- cache interface makes it annoying to pass
                        -- in auxiliary information
       find_package m
     LookupMultiple rs ->
       return (FoundMultiple rs)
     LookupHidden pkg_hiddens mod_hiddens ->
       return (NotFound{ fr_paths = [], fr_pkg = Nothing
                       , fr_pkgs_hidden = map (moduleUnitId.fst) pkg_hiddens
                       , fr_mods_hidden = map (moduleUnitId.fst) mod_hiddens
                       , fr_suggestions = [] })
     LookupNotFound suggest ->
       return (NotFound{ fr_paths = [], fr_pkg = Nothing
                       , fr_pkgs_hidden = []
                       , fr_mods_hidden = []
                       , fr_suggestions = suggest })

findPackageModule :: DynFlags -> (Module -> Action FindResult)
findPackageModule dflags mod = do
  let
        pkg_id = moduleUnitId mod
  --
  case lookupPackage dflags pkg_id of
     Nothing -> return (NoPackage pkg_id)
     Just pkg_conf -> findPackageModule_ dflags mod pkg_conf

findPackageModule_ :: DynFlags -> Module -> PackageConfig -> Action FindResult
findPackageModule_ dflags mod pkg_conf =

  -- special case for GHC.Prim; we won't find it in the filesystem.
  if mod == gHC_PRIM
        then return (Found (error "GHC.Prim ModLocation") mod)
        else

  let
     tag = buildTag dflags

           -- hi-suffix for packages depends on the build tag.
     package_hisuf | null tag  = "hi"
                   | otherwise = tag ++ "_hi"

     mk_hi_loc f s = mkHiOnlyModLocation dflags package_hisuf f s

     import_dirs = importDirs pkg_conf
      -- we never look for a .hi-boot file in an external package;
      -- .hi-boot files only make sense for the home package.
  in
  case import_dirs of
    [one] | MkDepend <- ghcMode dflags -> do
          -- there's only one place that this .hi file can be, so
          -- don't bother looking for it.
          let basename = moduleNameSlashes (moduleName mod)
              loc = mk_hi_loc one basename
          return (Found loc mod)
    _otherwise ->
          searchPathExts import_dirs mod [(package_hisuf, mk_hi_loc)]

-- NB: mb_mainFile is to tell where to find the Main file.  In general,
-- ALL file targets could contribute extra found modules, but we're
-- only supporting main for now.
findHomeModule :: DynFlags -> Maybe FilePath -> (ModuleName -> Action FindResult)
findHomeModule dflags mb_mainFile mod_name =
   let
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
                | mod_name == mkModuleName "Main" -> do
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

mkHiOnlyModLocation :: DynFlags -> Suffix -> FilePath -> String
                    -> ModLocation
mkHiOnlyModLocation dflags hisuf path basename
    = let full_basename = path </> basename
          obj_fn = mkObjPath  dflags full_basename basename
      in ModLocation{    ml_hs_file   = Nothing,
                             ml_hi_file   = full_basename <.> hisuf,
                                -- Remove the .hi-boot suffix from
                                -- hi_file, if it had one.  We always
                                -- want the name of the real .hi file
                                -- in the ml_hi_file field.
                             ml_obj_file  = obj_fn
                    }

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
                                 , fr_pkg   = Just (moduleUnitId mod)
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

-- | If there is no -o option, guess the name of target executable
-- by using top-level source file name as a base.
--
-- Original was in the Ghc monad but we don't want that
guessOutputFile :: FilePath -> FilePath
guessOutputFile mainModuleSrcPath =
    let name = dropExtension mainModuleSrcPath
    in if name == mainModuleSrcPath
        then throwGhcException . UsageError $
                 "default output name would overwrite the input file; " ++
                 "must specify -o explicitly"
        else name
