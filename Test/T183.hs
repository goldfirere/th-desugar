{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

#if __GLASGOW_HASKELL__ >= 907
{-# LANGUAGE NoFieldSelectors #-}
#endif

-- | A regression test for #T183 which ensures that 'lookupValueNameWithLocals'
-- does not reify a field selector when the @NoFieldSelectors@ language
-- extension is set on GHC 9.8 or later. We define this test in its own module
-- to avoid having to enable @NoFieldSelectors@ in other parts of the test
-- suite.
module T183 (t183) where

import Language.Haskell.TH (Name)
#if __GLASGOW_HASKELL__ >= 907
import Language.Haskell.TH.Desugar
#endif

t183 :: Maybe Name
#if __GLASGOW_HASKELL__ >= 907
-- This should return 'Nothing', as the 'unT' record should not be made into a
-- top-level field selector due to @NoFieldSelectors@.
t183 =
  $(do decs <- [d| data T = MkT { unT :: Int } |]
       mbName <- withLocalDeclarations decs (lookupValueNameWithLocals "unT")
       [| mbName |])
#else
-- Lacking @NoFieldSelectors@ on older versions of GHC, we simply hard-code the
-- result to 'Nothing'.
t183 = Nothing
#endif
