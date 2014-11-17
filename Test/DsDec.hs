{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes #-}
#if __GLASGOW_HASKELL__ >= 707
{-# LANGUAGE RoleAnnotations #-}
#endif

{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-incomplete-patterns
                -fno-warn-name-shadowing #-}

module Test.DsDec where

import qualified Test.Splices as S
import Test.Splices ( dsDecSplice, unqualify )

import Language.Haskell.TH  ( reportError )
import Language.Haskell.TH.Desugar

import Control.Monad

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

$(do decs <- S.rec_sel_test
     [DDataD nd [] name [DPlainTV tvbName] cons []] <- dsDecs decs
     let arg_ty = (DConT name) `DAppT` (DVarT tvbName)
     recsels <- fmap concat $ mapM (getRecordSelectors arg_ty) cons
     let num_sels = length recsels `div` 2 -- ignore type sigs
     when (num_sels /= S.rec_sel_test_num_sels) $
       reportError $ "Wrong number of record selectors extracted.\n"
                  ++ "Wanted " ++ show S.rec_sel_test_num_sels
                  ++ ", Got " ++ show num_sels
     let unrecord c@(DCon _ _ _ (DNormalC {})) = c
         unrecord (DCon tvbs cxt con_name (DRecC fields)) =
           let (_names, stricts, types) = unzip3 fields
               fields' = zip stricts types
           in
           DCon tvbs cxt con_name (DNormalC fields')
         plaindata = [DDataD nd [] name [DPlainTV tvbName] (map unrecord cons) []]
     return (decsToTH plaindata ++ map letDecToTH recsels))

