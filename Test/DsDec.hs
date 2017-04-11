{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes,
             StandaloneDeriving, DefaultSignatures,
             ConstraintKinds #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif
#if __GLASGOW_HASKELL__ >= 801
{-# LANGUAGE DerivingStrategies #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-incomplete-patterns
                -fno-warn-name-shadowing #-}

#if __GLASGOW_HASKELL__ >= 711
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
#endif

module DsDec where

import qualified Splices as S
import Splices ( dsDecSplice, unqualify )

import Language.Haskell.TH  ( reportError )
import Language.Haskell.TH.Desugar

import Control.Monad
import Data.Maybe( mapMaybe )

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

#if __GLASGOW_HASKELL__ >= 709
$(dsDecSplice S.dectest11)
$(dsDecSplice S.standalone_deriving_test)
#endif

#if __GLASGOW_HASKELL__ >= 801
$(dsDecSplice S.deriv_strat_test)
#endif

$(dsDecSplice S.dectest12)
$(dsDecSplice S.dectest13)

$(do decs <- S.rec_sel_test
     [DDataD nd [] name [DPlainTV tvbName] cons []] <- dsDecs decs
     let arg_ty = (DConT name) `DAppT` (DVarT tvbName)
     recsels <- getRecordSelectors arg_ty cons
     let num_sels = length recsels `div` 2 -- ignore type sigs
     when (num_sels /= S.rec_sel_test_num_sels) $
       reportError $ "Wrong number of record selectors extracted.\n"
                  ++ "Wanted " ++ show S.rec_sel_test_num_sels
                  ++ ", Got " ++ show num_sels
     let unrecord c@(DCon _ _ _ (DNormalC {}) _) = c
         unrecord (DCon tvbs cxt con_name (DRecC fields) rty) =
           let (_names, stricts, types) = unzip3 fields
               fields' = zip stricts types
           in
           DCon tvbs cxt con_name (DNormalC fields') rty
         plaindata = [DDataD nd [] name [DPlainTV tvbName] (map unrecord cons) []]
     return (decsToTH plaindata ++ mapMaybe letDecToTH recsels))
