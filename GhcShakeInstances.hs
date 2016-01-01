{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
module GhcShakeInstances where

-- stuff in this module is slow to compile, so split it out

import GhcPlugins hiding (varName)
import Fingerprint
import HscTypes
import Unique
import OccName
import DriverPhases

import GHC.Generics (Generic)

import Development.Shake.Rule
import Development.Shake.Classes
import Data.Binary (getWord8, putWord8)

-- UnitId
instance Show UnitId where
    show = unitIdString
instance Binary UnitId where
    put = put . unitIdFS
    get = fmap fsToUnitId get
instance NFData UnitId where
    rnf s = s `seq` ()
instance Hashable UnitId where
    hashWithSalt s a = getKey (getUnique a) + s

-- ModuleName
instance Show ModuleName where
    show = moduleNameString
instance Binary ModuleName where
    put = put . moduleNameFS
    get = fmap mkModuleNameFS get
instance Hashable ModuleName where
    hashWithSalt s a = getKey (getUnique a) + s
instance NFData ModuleName where
    rnf s = s `seq` ()

-- Module
instance Show Module where
    show m = show (moduleUnitId m) ++ ":"
          ++ show (moduleName m)
instance NFData Module where
    rnf a = a `seq` ()
instance Binary Module where
    put m = do
         put (moduleUnitId m)
         put (moduleName m)
    get = do
        uid <- get
        mod_name <- get
        return (mkModule uid mod_name)
instance Hashable Module where
    hashWithSalt s a = getKey (getUnique a) + s

-- OccName
instance Show OccName where
    show occ = occNameString occ ++ "{" ++ show (occNameSpace occ) ++ "}"
instance NFData OccName where
    rnf a = a `seq` ()
instance Binary OccName where
    put occ = do
        putWord8 $ case occNameSpace occ of
                    n | n == tcName   -> 0
                      | n == dataName -> 1
                      | n == tvName   -> 2
                      | n == varName  -> 3
                      | otherwise -> error "what is this! 2"
        put (occNameFS occ)
    get = do
        tag <- getWord8
        fs <- get
        let ns = case tag of
                    0 -> tcName
                    1 -> dataName
                    2 -> tvName
                    3 -> varName
                    _ -> error "what is this! 3"
        return (mkOccNameFS ns fs)
instance Hashable OccName where
    hashWithSalt s a = getKey (getUnique a) + s

-- NameSpace
instance Show NameSpace where
    show n | n == tcName = "tc"
           | n == dataName = "d"
           | n == tvName = "tv"
           | n == varName = "v"
           | otherwise = error "what is this!"

-- FastString
instance Binary FastString where
    put = put . fastStringToByteString
    get = fmap mkFastStringByteString get
instance NFData FastString where
    rnf s = s `seq` ()
instance Hashable FastString where
    hashWithSalt s fs = getKey (getUnique fs) + s

-- Fingerprint
instance Hashable Fingerprint where
    hashWithSalt s (Fingerprint w1 w2) = hashWithSalt s (w1, w2)

-- HscSource
deriving instance Generic HscSource
deriving instance Typeable HscSource
instance NFData HscSource
instance Binary HscSource
instance Hashable HscSource

-- Phase
deriving instance Generic Phase
deriving instance Typeable Phase
instance NFData Phase
instance Binary Phase
instance Hashable Phase

-- | A 'BuildModule' is a key for module which can be built.  Unlike
-- in 'GhcMake', we also store the source filename (because a module
-- may be implemented multiple times by different source files.)
data BuildModule
    = BuildModule {
        bm_filename :: FilePath,
        bm_mod :: Module,
        bm_is_boot :: IsBoot
        }
    deriving (Show, Typeable, Eq, Generic)
type IsBoot = Bool

instance Hashable BuildModule
instance Binary BuildModule
instance NFData BuildModule

-- | A 'RecompKey' is a key for a hash, for which recompilation can
-- be predicated on.  Each hash represents some aspect of a module
-- which you could depend on.
data RecompKey
    -- | The flags which were passed to compile a module.
    = FlagHash Module
    -- | The export list of a (boot) module
    | ExportHash Module IsBoot
    -- | The entire interface of the module
    | ModuleHash Module -- external package deps CANNOT be on boot
    -- | The declaration hash of a specific named entity
    | DeclHash Module IsBoot OccName
    deriving (Show, Typeable, Eq, Generic)

instance Hashable RecompKey
instance Binary RecompKey
instance NFData RecompKey

-- ModLocation
deriving instance Generic ModLocation
deriving instance Eq ModLocation
instance Hashable ModLocation
instance Binary ModLocation
instance NFData ModLocation
