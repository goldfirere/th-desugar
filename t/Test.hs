
module Main (main) where

import Foo
import Language.Haskell.TH.Syntax

main :: IO ()
main = do print $( lift (Foo "str1" 'c') )
          print $( lift (Bar "str2") )

