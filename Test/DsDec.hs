{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.DsDec where

import qualified Test.Splices as S
import Test.Splices ( dsDecSplice, unqualify )

#if __GLASGOW_HASKELL__ < 707
import Language.Haskell.TH.Desugar.Sweeten
#endif

$(dsDecSplice S.dectest1)
$(dsDecSplice S.dectest2)
$(dsDecSplice S.dectest3)
$(dsDecSplice S.dectest4)
$(dsDecSplice S.dectest5)
$(dsDecSplice S.dectest6)
$(dsDecSplice S.dectest7)
$(dsDecSplice S.dectest8)
$(dsDecSplice S.dectest9)

$(dsDecSplice (fmap unqualify S.instance_test))

$(dsDecSplice (fmap unqualify S.imp_inst_test1))
$(dsDecSplice (fmap unqualify S.imp_inst_test2))
$(dsDecSplice (fmap unqualify S.imp_inst_test3))
$(dsDecSplice (fmap unqualify S.imp_inst_test4))

#if __GLASGOW_HASKELL__ < 707
$(return $ decsToTH [S.ds_dectest10])
#else
$(dsDecSplice S.dectest10)
#endif
