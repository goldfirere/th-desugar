{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
-- This module offers a simplified version of the "Data.Map.Ordered.Strict" API
-- that assumes left-biased indices everywhere and uses a different 'Semigroup'
-- instance (the one in this module uses @('<>') = 'union'@) and 'Monoid'
-- instance (the one in this module uses @'mappend' = 'union'@).
--
----------------------------------------------------------------------------
module Language.Haskell.TH.Desugar.OMap.Strict
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
import qualified Data.Map.Strict as M (Map)
import Data.Map.Ordered.Strict (Index)
import qualified Data.Map.Ordered.Strict as OM
import Language.Haskell.TH.Desugar.OMap (OMap(..))
import Prelude hiding (filter, lookup, null)

empty :: forall k v. OMap k v
empty = coerce (OM.empty @k @v)

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
union = coerce ((OM.|<>) @k @v)

unionWithKey :: Ord k => (k -> v -> v -> v) -> OMap k v -> OMap k v -> OMap k v
unionWithKey f = coerce (OM.unionWithL f)

delete :: forall k v. Ord k => k -> OMap k v -> OMap k v
delete = coerce (OM.delete @k @v)

filterWithKey :: Ord k => (k -> v -> Bool) -> OMap k v -> OMap k v
filterWithKey f = coerce (OM.filter f)

(\\) :: forall k v v'. Ord k => OMap k v -> OMap k v' -> OMap k v
(\\) = coerce ((OM.\\) @k @v @v')

intersection :: forall k v v'. Ord k => OMap k v -> OMap k v' -> OMap k v
intersection = coerce ((OM.|/\) @k @v @v')

intersectionWithKey :: Ord k => (k -> v -> v' -> v'') -> OMap k v -> OMap k v' -> OMap k v''
intersectionWithKey f = coerce (OM.intersectionWith f)

null :: forall k v. OMap k v -> Bool
null = coerce (OM.null @k @v)

size :: forall k v. OMap k v -> Int
size = coerce (OM.size @k @v)

member :: forall k v. Ord k => k -> OMap k v -> Bool
member = coerce (OM.member @k @v)

notMember :: forall k v. Ord k => k -> OMap k v -> Bool
notMember = coerce (OM.notMember @k @v)

lookup :: forall k v. Ord k => k -> OMap k v -> Maybe v
lookup = coerce (OM.lookup @k @v)

lookupIndex :: forall k v. Ord k => k -> OMap k v -> Maybe Index
lookupIndex = coerce (OM.findIndex @k @v)

lookupAt :: forall k v. Index -> OMap k v -> Maybe (k, v)
lookupAt i m = OM.elemAt @k @v (coerce m) i

fromList :: Ord k => [(k, v)] -> OMap k v
fromList l = coerce (OM.fromList l)

assocs :: forall k v. OMap k v -> [(k, v)]
assocs = coerce (OM.assocs @k @v)

toAscList :: forall k v. OMap k v -> [(k, v)]
toAscList = coerce (OM.toAscList @k @v)

toMap :: forall k v. OMap k v -> M.Map k v
toMap = coerce (OM.toMap @k @v)
