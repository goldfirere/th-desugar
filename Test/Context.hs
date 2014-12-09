{- Tests for the th-desugar package -}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes,
             StandaloneDeriving, DefaultSignatures #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-name-shadowing #-}

module Test.Context where

import Control.Monad.State (runStateT)
import Data.Map (empty)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar.Context (testContext)

import Data.Array (Array)
import Data.Array.Base (UArray, IArray) -- IArray is the most commonly available multi-param type class I could find

-- :info IArray says these instances exist:
--
-- instance IArray UArray Int -- Defined in ‘Data.Array.Base’
-- instance IArray UArray Float -- Defined in ‘Data.Array.Base’
-- instance IArray UArray Double -- Defined in ‘Data.Array.Base’
-- instance IArray UArray Char -- Defined in ‘Data.Array.Base’
-- instance IArray UArray Bool -- Defined in ‘Data.Array.Base’
-- instance IArray Array e -- Defined in ‘Data.Array.Base’

test40_cxt :: Q Exp
test40_cxt =
    do array <- [t|Array|]
       uarray <- [t|UArray|]
       bool <- [t|Bool|]
       bot <- [t|()|]
       ((a, b, c), _mp) <-
           runStateT
             (do a <- testContext (const False) [ClassP ''IArray [uarray, bool]] -- This instance exists
                 b <- testContext (const False) [ClassP ''IArray [uarray, bot]]  -- No such instance
                 c <- testContext (const False) [ClassP ''IArray [array, bot]]   -- This instance exists
                 return (a, b, c))
           empty
       [|($(boolE a), $(boolE b), $(boolE c)) :: (Bool, Bool, Bool)|]
    where
      boolE True = [|True|]
      boolE False = [|False|]
