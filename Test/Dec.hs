{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes,
             StandaloneDeriving, DefaultSignatures #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-name-shadowing #-}

module Dec where

import qualified Splices as S
import Splices ( unqualify )

$(S.dectest1)
$(S.dectest2)
$(S.dectest3)
$(S.dectest4)
$(S.dectest5)
$(S.dectest6)
$(S.dectest7)
$(S.dectest8)
$(S.dectest9)
$(S.dectest10)
#if __GLASGOW_HASKELL__ >= 709
$(S.dectest11)
#endif

$(fmap unqualify S.instance_test)

$(fmap unqualify S.imp_inst_test1)
$(fmap unqualify S.imp_inst_test2)
$(fmap unqualify S.imp_inst_test3)
$(fmap unqualify S.imp_inst_test4)

$(S.rec_sel_test)

