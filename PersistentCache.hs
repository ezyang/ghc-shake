{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveDataTypeable, ScopedTypeVariables, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module PersistentCache(
    addPersistentCache, askPersistentCache
    ) where

import Development.Shake
import Development.Shake.Rule
import Development.Shake.Classes
import Control.Applicative
import Prelude


newtype CacheQ question = CacheQ question
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)
newtype CacheA answer = CacheA answer
    deriving (Show, Typeable, Eq, Hashable, Binary, NFData)

instance (ShakeValue q, ShakeValue a) => Rule (CacheQ q) (CacheA a) where
    storedValueE _ _ = return NeverRecomp


-- | A persistent cache is a function from question type @q@, to an answer type @a@,
--   which is cached across runs to Shake.  Cached values are not
--   recomputed unless any of their dependencies change.
--
--   Persistent caches are used similarly to oracles, but unlike
--   oracles, they are not rerun every invocation of Shake.  Unlike
--   'newCache', these caches ARE saved to disk (and thus the value
--   must be serializable), and you are not allowed to have two
addPersistentCache :: (ShakeValue q, ShakeValue a) => (q -> Action a) -> Rules (q -> Action a)
addPersistentCache act = do
    rule $ \(CacheQ q) -> Just $ CacheA <$> act q
    return askPersistentCache


-- | Get information from a cached 'addPersistentCache'. The
-- question/answer types must match those provided to
-- 'addPersistentCache'.
askPersistentCache :: (ShakeValue q, ShakeValue a) => q -> Action a
askPersistentCache question = do CacheA answer <- apply1 $ CacheQ question; return answer
