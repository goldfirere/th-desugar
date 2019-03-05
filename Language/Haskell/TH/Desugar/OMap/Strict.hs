{- Language/Haskell/TH/Desugar/OMap/Strict.hs

(c) Daniel Wagner 2016-2018, Ryan Scott 2019
-}

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
----------------------------------------------------------------------------
module Language.Haskell.TH.Desugar.OMap.Strict
    ( OMap
    -- * Trivial maps
    , empty, singleton
    -- * Insertion
    -- | Conventions:
    --
    -- * The open side of an angle bracket points to an 'OMap'
    --
    -- * The pipe appears on the side whose indices take precedence if both sides contain the same key
    --
    -- * The left argument's indices are lower than the right argument's indices
    --
    -- * If both sides contain the same key, the tuple's value wins
    , (<|), (|<), (>|), (|>)
    , (<>|), (|<>)
    -- * Deletion
    , delete, filter, (\\)
    -- * Query
    , null, size, member, notMember, lookup
    -- * Indexing
    , Index, findIndex, elemAt
    -- * List conversions
    , fromList, assocs, toAscList
    ) where

import Data.Foldable (foldl')
import qualified Data.Map.Strict as M
import Language.Haskell.TH.Desugar.OMap.Internal hiding ((<|), (|<), (>|), (|>), fromList)
import Language.Haskell.TH.Desugar.OMapSetUtil
import Prelude hiding (filter, foldr, lookup, null)

infixr 5 <|, |< -- copy :
infixl 5 >|, |>

(<|) , (|<)  :: Ord k => (,)  k v -> OMap k v -> OMap k v
(>|) , (|>)  :: Ord k => OMap k v -> (,)  k v -> OMap k v

(k, v) <| OMap tvs kvs = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = maybe (nextLowerTag kvs) fst (M.lookup k tvs)

(k, v) |< o = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = nextLowerTag kvs
    OMap tvs kvs = delete k o

o >| (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = nextHigherTag kvs
    OMap tvs kvs = delete k o

OMap tvs kvs |> (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = maybe (nextHigherTag kvs) fst (M.lookup k tvs)

singleton :: k -> v -> OMap k v
singleton k v = OMap (M.singleton k (0, v)) (M.singleton 0 (k, v))

-- | If a key appears multiple times, the first occurrence is used for ordering
-- and the last occurrence is used for its value. The library author welcomes
-- comments on whether this default is sane.
fromList :: Ord k => [(k, v)] -> OMap k v
fromList = foldl' (|>) empty
