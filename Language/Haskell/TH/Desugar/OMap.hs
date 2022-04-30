{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.OMap
-- Copyright   :  (C) 2016-2018 Daniel Wagner, 2019 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An 'OMap' behaves much like a 'M.Map', with all the same asymptotics, but
-- also remembers the order that keys were inserted.
--
-- This module offers a simplified version of the "Data.Map.Ordered" API
-- that assumes left-biased indices everywhere and uses a different 'Semigroup'
-- instance (the one in this module uses @('<>') = 'union'@) and 'Monoid'
-- instance (the one in this module uses @'mappend' = 'union'@).
--
----------------------------------------------------------------------------
module Language.Haskell.TH.Desugar.OMap
    ( OMap(..)
    -- * Trivial maps
    , empty, singleton
    -- * Insertion
    , insertPre, insertPost, union, unionWithKey
    -- * Deletion
    , delete, filterWithKey, (\\), intersection, intersectionWithKey
    -- * Query
    , null, size, member, notMember, lookup
    -- * Indexing
    , Index, lookupIndex, lookupAt
    -- * List conversions
    , fromList, assocs, toAscList
    -- * 'M.Map' conversion
    , toMap
    ) where

import Data.Coerce
import Data.Data
import qualified Data.Map.Lazy as M (Map)
import Data.Map.Ordered (Bias(..), Index, L)
import qualified Data.Map.Ordered as OM
import Prelude hiding (filter, lookup, null)

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif

-- | An ordered map whose 'insertPre', 'insertPost', 'intersection',
-- 'intersectionWithKey', 'union', and 'unionWithKey' operations are biased
-- towards leftmost indices when when breaking ties between keys.
newtype OMap k v = OMap (Bias L (OM.OMap k v))
  deriving (Data, Foldable, Functor, Eq, Ord, Read, Show, Traversable, Typeable)

instance Ord k => Semigroup (OMap k v) where
  (<>) = union
instance Ord k => Monoid (OMap k v) where
  mempty = empty
#if !(MIN_VERSION_base(4,11,0))
  mappend = (<>)
#endif

empty :: forall k v. OMap k v
empty = coerce (OM.empty :: OM.OMap k v)

singleton :: k -> v -> OMap k v
singleton k v = coerce (OM.singleton (k, v))

-- | The value's index will be lower than the indices of the values in the
-- 'OSet'.
insertPre :: Ord k => k -> v -> OMap k v -> OMap k v
insertPre k v = coerce ((k, v) OM.|<)

-- | The value's index will be higher than the indices of the values in the
-- 'OSet'.
insertPost :: Ord k => OMap k v -> k -> v -> OMap k v
insertPost m k v = coerce (coerce m OM.|> (k, v))

union :: forall k v. Ord k => OMap k v -> OMap k v -> OMap k v
union = coerce ((OM.|<>) :: OM.OMap k v -> OM.OMap k v -> OM.OMap k v)

unionWithKey :: Ord k => (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithKey f = coerce (OM.unionWithL f)

delete :: forall k v. Ord k => k -> OMap k v -> OMap k v
delete = coerce (OM.delete :: k -> OM.OMap k v -> OM.OMap k v)

filterWithKey :: Ord k => (k -> v -> Bool) -> OMap k v -> OMap k v
filterWithKey f = coerce (OM.filter f)

(\\) :: forall k v v'. Ord k => OMap k v -> OMap k v' -> OMap k v
(\\) = coerce ((OM.\\) :: OM.OMap k v -> OM.OMap k v' -> OM.OMap k v)

intersection :: forall k v v'. Ord k => OMap k v -> OMap k v' -> OMap k v
intersection = coerce ((OM.|/\) :: OM.OMap k v -> OM.OMap k v' -> OM.OMap k v)

intersectionWithKey :: Ord k => (k -> v -> v' -> v'') -> OMap k v -> OMap k v' -> OMap k v''
intersectionWithKey f = coerce (OM.intersectionWith f)

null :: forall k v. OMap k v -> Bool
null = coerce (OM.null :: OM.OMap k v -> Bool)

size :: forall k v. OMap k v -> Int
size = coerce (OM.size :: OM.OMap k v -> Int)

member :: forall k v. Ord k => k -> OMap k v -> Bool
member = coerce (OM.member :: k -> OM.OMap k v -> Bool)

notMember :: forall k v. Ord k => k -> OMap k v -> Bool
notMember = coerce (OM.notMember :: k -> OM.OMap k v -> Bool)

lookup :: forall k v. Ord k => k -> OMap k v -> Maybe v
lookup = coerce (OM.lookup :: k -> OM.OMap k v -> Maybe v)

lookupIndex :: forall k v. Ord k => k -> OMap k v -> Maybe Index
lookupIndex = coerce (OM.findIndex :: k -> OM.OMap k v -> Maybe Index)

lookupAt :: forall k v. Index -> OMap k v -> Maybe (k, v)
lookupAt i m = coerce (OM.elemAt (coerce m) i :: Maybe (k, v))

fromList :: Ord k => [(k, v)] -> OMap k v
fromList l = coerce (OM.fromList l)

assocs :: forall k v. OMap k v -> [(k, v)]
assocs = coerce (OM.assocs :: OM.OMap k v -> [(k, v)])

toAscList :: forall k v. OMap k v -> [(k, v)]
toAscList = coerce (OM.toAscList :: OM.OMap k v -> [(k, v)])

toMap :: forall k v. OMap k v -> M.Map k v
toMap = coerce (OM.toMap :: OM.OMap k v -> M.Map k v)
