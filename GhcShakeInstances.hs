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

-- ModuleName
instance Show ModuleName where
    show = moduleNameString
instance Binary ModuleName where
    put = put . moduleNameFS
    get = fmap mkModuleNameFS get
instance Hashable ModuleName where
    hashWithSalt s a = getKey (getUnique a) + s

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

-- BuildModule
type IsBoot = Bool
data BuildModule -- this is what it's called in GhcMake
    = BuildModule FilePath Module IsBoot
    deriving (Show, Typeable, Eq, Generic)

instance Hashable BuildModule
instance Binary BuildModule
instance NFData BuildModule

-- RecompKey
data RecompKey
    = FlagHash Bool
    | ExportHash Module IsBoot
    | ModuleHash Module -- external package deps CANNOT be on boot
    | DeclHash Module IsBoot OccName
    deriving (Show, Typeable, Eq, Generic)

instance Hashable RecompKey
instance Binary RecompKey
instance NFData RecompKey