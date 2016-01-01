{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
module BuildModule (
    BuildModule(..),
    buildModuleLocation,
    buildModuleLocations,
    buildModuleRule,
    needBuildModule,
    shakeDynFlags,
    ) where

import GhcPlugins hiding ( varName, errorMsg, fatalErrorMsg )

import Maybes

import GhcShakeInstances
import Compat

import Development.Shake
import Development.Shake.Rule
import Development.Shake.Classes

-- I'm evil!
import Development.Shake.Rules.File
import Development.Shake.ByteString
import General.String

import Prelude hiding (mod)
import GHC.Generics (Generic)
import qualified Data.HashMap.Strict as HashMap
import Data.Dynamic
import System.FilePath

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

instance Hashable BuildModule
instance Binary BuildModule
instance NFData BuildModule

-- | Compute the 'ModLocation' for a 'BuildModule'.
buildModuleLocation :: DynFlags -> BuildModule -> ModLocation
buildModuleLocation dflags (BuildModule file mod is_boot) =
    let basename = dropExtension file
        mod_basename = moduleNameSlashes (moduleName mod)
        maybeAddBootSuffixLocn
            | is_boot   = addBootSuffixLocn
            | otherwise = id
    in maybeAddBootSuffixLocn
         $ ModLocation {
                ml_hs_file = Just file,
                ml_hi_file  = mkHiPath  dflags basename mod_basename,
                ml_obj_file = mkObjPath dflags basename mod_basename
            }

-- | Computes the normal and the dynamic (in that order) 'ModLocation's
-- of a 'BuildModule'.
buildModuleLocations :: DynFlags -> BuildModule -> (ModLocation, ModLocation)
buildModuleLocations dflags bm =
    let dyn_dflags = dynamicTooMkDynamicDynFlags dflags
    in (buildModuleLocation dflags bm, buildModuleLocation dyn_dflags bm)


-- | An answer type for 'BuildModule' rules, tracking the file state of
-- all possible files a 'BuildModule' rule may generate.
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


-- | Recompute 'BuildModuleA' based on the state of the file system
-- and what we were rebuilding this round.
rebuildBuildModuleA :: ShakeOptions -> BuildModule -> IO BuildModuleA
rebuildBuildModuleA opts bm = do
    let dflags = shakeDynFlags opts
    -- TODO: more sanity checking, e.g. make sure that things we
    -- expect were actually built
    r <- storedValue opts bm
    -- If we recompiled, we must invalidate anything we DIDN'T build
    -- (so the next time the are requested, we trigger a recomp.)
    let invalidateObj | hscTarget dflags == HscNothing = \bma -> bma { bma_o = Nothing }
                      | otherwise = id
        invalidateDyn | gopt Opt_BuildDynamicToo dflags = id
                      | otherwise = \bma -> bma { bma_dyn_hi = Nothing, bma_dyn_o = Nothing }
    case r of
        Nothing -> error "Missing compilation products"
        Just ans -> return (invalidateDyn (invalidateObj ans))


-- | Extract 'DynFlags' from 'ShakeOptions'.
shakeDynFlags :: ShakeOptions -> DynFlags
shakeDynFlags opts =
    case HashMap.lookup (typeRep (Proxy :: Proxy DynFlags)) (shakeExtra opts) of
        Nothing -> error "shakeDynFlags: not in map"
        Just d -> case fromDynamic d of
                    Just dflags -> dflags
                    Nothing -> error "shakeDynFlags: bad type"


-- | Create a 'FileQ' (the question type for Shake's built-in file
-- rules) from a 'FilePath'.
mkFileQ :: FilePath -> FileQ
mkFileQ = FileQ . packU_ . filepathNormalise . unpackU_ . packU

buildModuleRule :: (BuildModule -> Action ()) -> Rules ()
buildModuleRule f = rule $ \bm -> Just $ do
    f bm
    opts <- getShakeOptions
    liftIO $ rebuildBuildModuleA opts bm

-- This is similar to the Files rule, representing four files.  However,
-- we do not necessarily compare on ALL of them to determine whether
-- or not a stored value is valid: we only compare on the files which
-- we are BUILDING.
instance Rule BuildModule BuildModuleA where
    storedValue opts bm = do
        let dflags     = shakeDynFlags opts
            (loc, dyn_loc) = buildModuleLocations dflags bm
        mb_hi       <- storedValue opts (mkFileQ (ml_hi_file loc))
        mb_o        <- storedValue opts (mkFileQ (ml_obj_file loc))
        mb_dyn_hi   <- storedValue opts (mkFileQ (ml_hi_file dyn_loc))
        mb_dyn_o    <- storedValue opts (mkFileQ (ml_obj_file dyn_loc))
        return (Just (BuildModuleA mb_hi mb_o mb_dyn_hi mb_dyn_o))
    equalValue opts bm v1 v2 =
        let dflags = shakeDynFlags opts
            (loc, dyn_loc) = buildModuleLocations dflags bm
        in foldr and_ EqualCheap
            $ [ test (mkFileQ (ml_hi_file loc)) bma_hi ]
           ++ if hscTarget dflags == HscNothing
                then []
                else [ test (mkFileQ (ml_obj_file loc)) bma_o ]
                  ++ if gopt Opt_BuildDynamicToo dflags
                        then [ test (mkFileQ (ml_hi_file dyn_loc))  bma_dyn_hi
                             , test (mkFileQ (ml_obj_file dyn_loc)) bma_dyn_o ]
                        else []
      where test k sel = case equalValue opts k <$> sel v1 <*> sel v2 of
                            Nothing -> NotEqual
                            Just r -> r
            -- Copy-pasted from Shake
            and_ NotEqual _ = NotEqual
            and_ EqualCheap x = x
            and_ EqualExpensive x = if x == NotEqual then NotEqual else EqualExpensive

-- | Add a dependency on a Haskell module.
needBuildModule :: BuildModule -> Action ()
needBuildModule bm = (apply1 bm :: Action BuildModuleA) >> return ()
