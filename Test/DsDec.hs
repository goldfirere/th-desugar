{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE TemplateHaskell, GADTs, PolyKinds, TypeFamilies,
             MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, DataKinds, CPP, RankNTypes,
             StandaloneDeriving, DefaultSignatures,
             ConstraintKinds, RoleAnnotations, DeriveAnyClass,
             TypeApplications #-}
#if __GLASGOW_HASKELL__ >= 801
{-# LANGUAGE DerivingStrategies #-}
#endif
#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE StandaloneKindSignatures #-}
#endif
#if __GLASGOW_HASKELL__ >= 907
{-# LANGUAGE TypeAbstractions #-}
#endif

{-# OPTIONS_GHC -Wno-orphans -Wno-incomplete-patterns
                -Wno-name-shadowing -Wno-redundant-constraints #-}

module DsDec where

import qualified Splices as S
import Splices ( dsDecSplice, unqualify )

import qualified Language.Haskell.TH.Datatype.TyVarBndr as THAbs
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Syntax ( qReport )

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

$(dsDecSplice S.dectest10)

$(dsDecSplice S.dectest11)
$(dsDecSplice S.standalone_deriving_test)

#if __GLASGOW_HASKELL__ >= 801
$(dsDecSplice S.deriv_strat_test)
#endif

$(dsDecSplice S.dectest12)
$(dsDecSplice S.dectest13)
$(dsDecSplice S.dectest14)

$(dsDecSplice S.dectest15)

#if __GLASGOW_HASKELL__ >= 802
$(return $ decsToTH [S.ds_dectest16])
$(return $ decsToTH [S.ds_dectest17])
#endif

#if __GLASGOW_HASKELL__ >= 809
$(dsDecSplice S.dectest18)
#endif

#if __GLASGOW_HASKELL__ >= 907
$(dsDecSplice S.dectest19)
#endif

#if __GLASGOW_HASKELL__ >= 909
$(dsDecSplice S.dectest20)
#endif

$(do decs <- S.rec_sel_test
     withLocalDeclarations decs $ do
       [DDataD nd [] name [DPlainTV tvbName THAbs.BndrReq] k cons []] <- dsDecs decs
       recsels <- getRecordSelectors cons
       let num_sels = length recsels `div` 2 -- ignore type sigs
       when (num_sels /= S.rec_sel_test_num_sels) $
         qReport True $ "Wrong number of record selectors extracted.\n"
                     ++ "Wanted " ++ show S.rec_sel_test_num_sels
                     ++ ", Got " ++ show num_sels
       let unrecord c@(DCon _ _ _ (DNormalC {}) _) = c
           unrecord (DCon tvbs cxt con_name (DRecC fields) rty) =
             let (_names, stricts, types) = unzip3 fields
                 fields' = zip stricts types
             in
             DCon tvbs cxt con_name (DNormalC False fields') rty
           plaindata = [DDataD nd [] name [DPlainTV tvbName THAbs.BndrReq] k (map unrecord cons) []]
       return (decsToTH plaindata ++ map letDecToTH recsels))
