{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module      : GhcAction
Description : Reimplemented GHC functionality in the Action monad
Copyright   : (c) Edward Z. Yang, 2015-2016
License     : BSD3
Maintainer  : ezyang@cs.stanford.edu
Stability   : experimental
Portability : portable

A lot of behavior (e.g., how an @.o@ file is to be made) depends
on our ability to actually find the relevant Haskell source file.
In GHC, the 'Finder' is responsible for implementing this logic
in the 'IO' monad.

However, finder actions are relevant for recompilation in the
build system.  Thus, we reimplement them here in the 'Action'
monad so that we can track them, and trigger a rebuild when the
result of a finder would have changed.

Shake caches the results of these, so we have to use a simplified
'FindResult' type which is 'Maybe (ModLocation, Module)'.
-}
module GhcAction where

import GhcPlugins hiding ( varName )
import PrelNames ( gHC_PRIM )
import Finder ( mkHomeModLocation )
import Packages ( lookupModuleWithSuggestions )

import GhcShakeInstances ()
import Compat
import PersistentCache

import Development.Shake
import Development.Shake.Classes

import Prelude hiding (mod)
import qualified Data.Map as Map
import Data.Map (Map)
import System.FilePath

-- | Reimplementation of GHC's @findImportedModule@: given a module name
-- and possibly a package qualifying string (as in an @import "pkg"
-- ModName@ statement), find the 'ModLocation' and 'Module' that GHC
-- would consider this import pointing to.
findImportedModule :: ModuleName -> Maybe FastString
                    -> Action (Maybe (ModLocation, Module))
findImportedModule mod_name mb_pkg =
  case mb_pkg of
        Nothing                        -> unqual_import
        Just pkg | pkg == fsLit "this" -> home_import -- "this" is special
                 | otherwise           -> pkg_import
  where
    home_import   = findHomeModule mod_name

    pkg_import    = findExposedPackageModule (mod_name, mb_pkg)

    unqual_import = findHomeModule mod_name
                    `orIfNotFound`
                    findExposedPackageModule (mod_name, Nothing)

-- | Reimplementation of GHC's @findExactModule@: given a fully
-- qualified 'Module', find the 'ModLocation' and 'Module' that GHC
-- would consider this import pointing to.
findExactModule :: DynFlags -> Module -> Action (Maybe (ModLocation, Module))
findExactModule dflags mod =
    if moduleUnitId mod == thisPackage dflags
       then findHomeModule (moduleName mod)
       else findPackageModule mod

-- | THIS IS AN ORACLE.  A simplification of GHC's
-- @lookupModuleWithSuggestions@, which is oracle'ized so we don't have
-- to have an in-depth understanding of how GHC's package database is
-- setup.  (Oracle overhead will scale linearly with the number of
-- imports, but these queries should all be quick lookups into the
-- package database state.)
lookupModule :: (ModuleName, Maybe FastString) -> Action (Maybe Module)
lookupModule = askOracle

-- | The backing implementation of 'lookupModule', to be passed to
-- 'addOracle'.
lookupModule' :: DynFlags -> (ModuleName, Maybe FastString) -> Action (Maybe Module)
lookupModule' dflags (mod_name, mb_pkg) =
    case lookupModuleWithSuggestions dflags mod_name mb_pkg of
        LookupFound m _ -> return (Just m)
        _ -> return Nothing

-- | Reimplementation of GHC's @findExposedPackageModule@: given a
-- user import which is known not to be a home module, find it from
-- the package database.
findExposedPackageModule :: (ModuleName, Maybe FastString)
                         -> Action (Maybe (ModLocation, Module))
findExposedPackageModule (mod_name, mb_pkg) = do
    mb_m <- lookupModule (mod_name, mb_pkg)
    case mb_m of
        Nothing -> return Nothing
        Just m -> findPackageModule m

-- | THIS IS A PERSISTENT CACHE.  Reimplementation of GHC's
-- @findPackageModule@: given a fully qualified 'Module', find the
-- location of its interface files.  (This also returns the 'Module' for
-- consistency; it's expected to be equal to the input.)
findPackageModule :: Module -> Action (Maybe (ModLocation, Module))
findPackageModule = askPersistentCache

-- | The backing implementation of 'findPackageModule', to be passed to
-- 'addPersistentCache'.
findPackageModule' :: DynFlags -> (Module -> Action (Maybe (ModLocation, Module)))
findPackageModule' dflags mod = do
  let
        pkg_id = moduleUnitId mod
  --
  case lookupPackage dflags pkg_id of
     Nothing -> return Nothing
     Just pkg_conf -> findPackageModule_ dflags mod pkg_conf

-- | Reimplementation of GHC's @findPackageModule_@, a helper function
-- which also has the 'PackageConfig' for the module.
--
-- TODO: PackageConfig should be oracle'ized, so that if a packagedb
-- entry changes we recompile correctly, or the package database
-- treated more correctly.
findPackageModule_ :: DynFlags -> Module -> PackageConfig -> Action (Maybe (ModLocation, Module))
findPackageModule_ dflags mod pkg_conf =

  -- special case for GHC.Prim; we won't find it in the filesystem.
  if mod == gHC_PRIM
        then return Nothing
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
          return (Just (loc, mod))
    _otherwise ->
          searchPathExts import_dirs mod [(package_hisuf, mk_hi_loc)]

-- | THIS IS A PERSISTENT CACHE.  A reimplementation of GHC's
-- @findHomeModule@: given a 'ModuleName' find the location of the home
-- module that implements it.
findHomeModule :: ModuleName -> Action (Maybe (ModLocation, Module))
findHomeModule = askPersistentCache

-- | The backing implementation of 'findHomeModule', to be passed to
-- 'addPersistentCache'.
findHomeModule' :: DynFlags
                -> (ModuleName -> Action (Maybe (ModLocation, Module)))
findHomeModule' dflags mod_name =
   let
     home_path = importPaths dflags
     mod = mkModule (thisPackage dflags) mod_name

     exts =
      [ ("hs",   mkHomeModLocationSearched dflags mod_name "hs")
      , ("lhs",  mkHomeModLocationSearched dflags mod_name "lhs")
      , ("hsig",  mkHomeModLocationSearched dflags mod_name "hsig")
      , ("lhsig",  mkHomeModLocationSearched dflags mod_name "lhsig")
      ]

   in
  if mod == gHC_PRIM
    then return Nothing
    else
        do mb_file <- askModuleNameFile mod_name
           case mb_file of
                Just file -> do
                    loc <- liftIO $ mkHomeModLocation dflags mod_name file
                    return (Just (loc, mod))
                _ -> searchPathExts home_path mod exts

-- | Newtype for 'askFileModuleName' question type.
newtype FileModuleName = FileModuleName FilePath
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

-- | THIS IS AN ORACLE.  Given a file, this says what the module name
-- name of it is.  It's an oracle because this mapping depends on what
-- command line arguments are passed to GHC.
askFileModuleName :: FilePath -> Action ModuleName
askFileModuleName = askOracle . FileModuleName

-- | The backing implementation of 'askFileModuleName', to be passed
-- to 'addOracle'.
askFileModuleName' :: Map FilePath ModuleName -> FileModuleName -> Action ModuleName
askFileModuleName' file_to_mod_name (FileModuleName file) =
    case Map.lookup file file_to_mod_name of
        Nothing -> error "illegal file"
        Just mod_name -> return mod_name

-- | Newtype for 'askModuleNameFile' question type.
newtype ModuleNameFile = ModuleNameFile ModuleName
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

-- | THIS IS AN ORACLE.  Given a module name, is there a file which
-- implements it which was EXPLICITLY requested in the command line.
-- It's an oracle because this mapping depends on what command line
-- arguments are passed to GHC.
askModuleNameFile :: ModuleName -> Action (Maybe FilePath)
askModuleNameFile = askOracle . ModuleNameFile

-- | The backing implementation of 'askModuleNameFile', to be passed
-- to 'addOracle'
askModuleNameFile' :: ModuleNameEnv FilePath -> ModuleNameFile -> Action (Maybe FilePath)
askModuleNameFile' mod_name_to_file (ModuleNameFile mod_name) = return (lookupUFM mod_name_to_file mod_name)

type FileExt = String
type BaseName = String

-- | Pure reimplementation of GHC's @mkHomeModLocationSearched@.
mkHomeModLocationSearched :: DynFlags -> ModuleName -> FileExt
                          -> FilePath -> BaseName -> ModLocation
mkHomeModLocationSearched dflags mod suff path basename =
   mkHomeModLocation2 dflags mod (if path == "." then basename
                                                 else path </> basename) suff

-- | Pure reimplementation of GHC's @mkHomeModLocation2@.
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

-- | Pure reimplementation of GHC's @mkHiOnlyModLocation@.
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

-- | Reimplementation of GHC's @searchPathExts@, but tracking where
-- was probed.
searchPathExts
  :: [FilePath]         -- paths to search
  -> Module             -- module name
  -> [ (
        FileExt,                             -- suffix
        FilePath -> BaseName -> ModLocation  -- action
       )
     ]
  -> Action (Maybe (ModLocation, Module))

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

    search [] = return Nothing

    search ((file, loc) : rest) = do
      b <- doesFileExist file
      if b
        then return (Just (loc, mod))
        else search rest

-- | Reimplementation of GHC's @orIfNotFound@, but on a simplified type.
orIfNotFound :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
orIfNotFound this or_this = do
  res <- this
  case res of
    Nothing -> or_this
    _ -> return res
