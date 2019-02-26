{- Language/Haskell/TH/Desugar/OSet.hs

(c) Daniel Wagner 2016-2018, Ryan Scott 2019
-}

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
----------------------------------------------------------------------------
module Language.Haskell.TH.Desugar.OSet
    ( OSet
    -- * Trivial sets
    , empty, singleton
    -- * Insertion
    -- | Conventionts:
    --
    -- * The open side of an angle bracket points to an 'OSet'
    --
    -- * The pipe appears on the side whose indices take precedence for keys that appear on both sides
    --
    -- * The left argument's indices are lower than the right argument's indices
    , (<|), (|<), (>|), (|>)
    , (<>|), (|<>)
    -- * Query
    , null, size, member, notMember
    -- * Deletion
    , delete, filter, (\\), intersection
    -- * Indexing
    , Index, findIndex, elemAt
    -- * List conversions
    , fromList, toAscList
    ) where

import qualified Data.Set as S ()
import Language.Haskell.TH.Desugar.OMapSetUtil
import Language.Haskell.TH.Desugar.OSet.Internal
import Prelude hiding (filter, foldr, lookup, null)
