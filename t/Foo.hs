{-# LANGUAGE TemplateHaskell #-}
module Foo where

import Language.Haskell.TH.Lift

data Foo a = Foo a Char | Bar a
    deriving Show

newtype Rec a = Rec { field :: a }
                deriving Show

$(deriveLift ''Foo)
$(deriveLift ''Rec)
