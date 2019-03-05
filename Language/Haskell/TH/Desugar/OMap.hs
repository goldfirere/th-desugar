{- Language/Haskell/TH/Desugar/OMap.hs

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
module Language.Haskell.TH.Desugar.OMap
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

import qualified Data.Map.Lazy as M
import Language.Haskell.TH.Desugar.OMap.Internal
import Language.Haskell.TH.Desugar.OMapSetUtil
import Prelude hiding (filter, foldr, lookup, null)

singleton :: k -> v -> OMap k v
singleton k v = OMap (M.singleton k (0, v)) (M.singleton 0 (k, v))
