{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Foo where

import Language.Haskell.TH.Lift

-- Phantom type parameters can't be dealt with poperly on GHC < 7.8.
#if MIN_VERSION_template_haskell(2,9,0)
data (Eq a) => Foo a b = Foo a Char | Bar a
#else
data (Eq a) => Foo a = Foo a Char | Bar a
#endif
    deriving Show

newtype Rec a = Rec { field :: a }
                deriving Show

$(deriveLift ''Foo)
$(deriveLift ''Rec)
