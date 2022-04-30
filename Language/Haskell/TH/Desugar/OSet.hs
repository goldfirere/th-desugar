{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.OSet
-- Copyright   :  (C) 2016-2018 Daniel Wagner, 2019 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- An 'OSet' behaves much like a 'S.Set', with all the same asymptotics, but
-- also remembers the order that values were inserted.
--
-- This module offers a simplified version of the "Data.Set.Ordered" API
-- that assumes left-biased indices everywhere.
--
----------------------------------------------------------------------------
module Language.Haskell.TH.Desugar.OSet
    ( OSet
    -- * Trivial sets
    , empty, singleton
    -- * Insertion
    , insertPre, insertPost, union
    -- * Query
    , null, size, member, notMember
    -- * Deletion
    , delete, filter, (\\), intersection
    -- * Indexing
    , Index, lookupIndex, lookupAt
    -- * List conversions
    , fromList, toAscList
    -- * 'Set' conversion
    , toSet
    ) where

import Data.Coerce
import Data.Data
import qualified Data.Set as S (Set)
import Data.Set.Ordered (Bias(..), Index, L)
import qualified Data.Set.Ordered as OS
import Language.Haskell.TH.Desugar.OMap ()
import Prelude hiding (filter, null)

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif

-- | An ordered set whose 'insertPre', 'insertPost', 'intersection', and 'union'
-- operations are biased towards leftmost indices when when breaking ties
-- between keys.
newtype OSet a = OSet (Bias L (OS.OSet a))
  deriving (Data, Foldable, Eq, Monoid, Ord, Read, Show, Typeable)

instance Ord a => Semigroup (OSet a) where
  (<>) = union

empty :: forall a. OSet a
empty = coerce (OS.empty :: OS.OSet a)

singleton :: a -> OSet a
singleton a = coerce (OS.singleton a)

-- | The element's index will be lower than the indices of the elements in the
-- 'OSet'.
insertPre :: Ord a => a -> OSet a -> OSet a
insertPre a = coerce (a OS.|<)

-- | The element's index will be higher than the indices of the elements in the
-- 'OSet'.
insertPost :: Ord a => OSet a -> a -> OSet a
insertPost s a = coerce (coerce s OS.|> a)

union :: forall a. Ord a => OSet a -> OSet a -> OSet a
union = coerce ((OS.|<>) :: OS.OSet a -> OS.OSet a -> OS.OSet a)

null :: forall a. OSet a -> Bool
null = coerce (OS.null :: OS.OSet a -> Bool)

size :: forall a. OSet a -> Int
size = coerce (OS.size :: OS.OSet a -> Int)

member, notMember :: Ord a => a -> OSet a -> Bool
member    a = coerce (OS.member a)
notMember a = coerce (OS.notMember a)

delete :: Ord a => a -> OSet a -> OSet a
delete a = coerce (OS.delete a)

filter :: Ord a => (a -> Bool) -> OSet a -> OSet a
filter f = coerce (OS.filter f)

(\\) :: forall a. Ord a => OSet a -> OSet a -> OSet a
(\\) = coerce ((OS.\\) :: OS.OSet a -> OS.OSet a -> OS.OSet a)

intersection :: forall a. Ord a => OSet a -> OSet a -> OSet a
intersection = coerce ((OS.|/\) :: OS.OSet a -> OS.OSet a -> OS.OSet a)

lookupIndex :: Ord a => a -> OSet a -> Maybe Index
lookupIndex a = coerce (OS.findIndex a)

lookupAt :: forall a. Index -> OSet a -> Maybe a
lookupAt i s = coerce (OS.elemAt (coerce s) i :: Maybe a)

fromList :: Ord a => [a] -> OSet a
fromList l = coerce (OS.fromList l)

toAscList :: forall a. OSet a -> [a]
toAscList = coerce (OS.toAscList :: OS.OSet a -> [a])

toSet :: forall a. OSet a -> S.Set a
toSet = coerce (OS.toSet :: OS.OSet a -> S.Set a)
