{-# LANGUAGE MagicHash #-}

-- | Defines data types with names identical to those found in "GHC.Types".
-- This is used as part of a series of unit tests for the
-- @unboxedSumNameDegree_maybe@ function, which should only return 'Just' when the
-- argument 'Name' is actually an unboxed sum from "GHC.Types", not a user-defined
-- type.
module FakeSums
  ( Sum2#, Sum3#, Sum4#
  ) where

data Sum2# a b
data Sum3# a b c
data Sum4# a b c
