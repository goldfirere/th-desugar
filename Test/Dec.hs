{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes,
             StandaloneDeriving, DefaultSignatures,
             ConstraintKinds, RoleAnnotations, DeriveAnyClass #-}

{-# OPTIONS_GHC -Wno-orphans -Wno-name-shadowing
                -Wno-redundant-constraints #-}

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
$(S.dectest11)
$(S.dectest12)
$(S.dectest13)
$(S.dectest14)

$(S.dectest15)

#if __GLASGOW_HASKELL__ >= 802
$(S.dectest16)
$(S.dectest17)
#endif

#if __GLASGOW_HASKELL__ >= 809
$(S.dectest18)
#endif

$(fmap unqualify S.instance_test)

$(fmap unqualify S.imp_inst_test1)
$(fmap unqualify S.imp_inst_test2)
$(fmap unqualify S.imp_inst_test3)
$(fmap unqualify S.imp_inst_test4)

$(S.rec_sel_test)
