{-# LANGUAGE MagicHash #-}

-- | Defines data types with names identical to those found in "GHC.Tuple".
-- This is used as part of a series of unit tests for the
-- @tupleNameDegree_maybe@ and @unboxedTupleNameDegree_maybe@ functions, which
-- should only return 'Just' when the argument 'Name' is actually a tuple from
-- "GHC.Tuple", not a user-defined type.
module FakeTuples
  ( Tuple0,  Tuple1,  Tuple2,  Tuple3
  , Tuple0#, Tuple1#, Tuple2#, Tuple3#
  ) where

data Tuple0
data Tuple1 a
data Tuple2 a b
data Tuple3 a b c

data Tuple0#
data Tuple1# a
data Tuple2# a b
data Tuple3# a b c
