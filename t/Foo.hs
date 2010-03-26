
module Foo where

import Language.Haskell.TH.Lift

data Foo a = Foo a Char | Bar a
    deriving Show

$(deriveLift ''Foo)

