{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

-- | A regression test for #158 which ensures that lambda expressions
-- containing patterns with unlifted types desugar as expected. We define this
-- test in its own module, without UnboxedTuples enabled, to ensure that users
-- do not have to enable the extension themselves.
module T158Exp where

import Language.Haskell.TH.Desugar

t158 :: ()
t158 =
  $([| (\27# 42# -> ()) 27# 42# |] >>= dsExp >>= return . expToTH)
