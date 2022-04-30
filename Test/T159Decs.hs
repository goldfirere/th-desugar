{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

-- | Defines two non-exhaustive functions that roundtrip through desugaring
-- and sweetening. Both of these functions should desugar to definitions that
-- throw a runtime exception before forcing their argument.
--
-- Because these functions are non-exhaustive (and therefore emit warnings), we
-- put them in their own module so that we can disable the appropriate warnings
-- without needing to disable the warnings globally.
module T159Decs
  ( t159A, t159B
  ) where

import Splices ( dsDecSplice )

$(dsDecSplice [d| t159A, t159B :: () -> IO ()
                  t159A x | False = return ()
                  t159B x = case x of y | False -> return ()
                |])
