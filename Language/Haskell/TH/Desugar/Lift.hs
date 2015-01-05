-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Lift
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Defines @Lift@ instances for the desugared language. This is defined
-- in a separate module because it also must define @Lift@ instances for
-- several TH types, which are orphans and may want another definition
-- downstream.
--
----------------------------------------------------------------------------

{-# LANGUAGE CPP, TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Haskell.TH.Desugar.Lift () where

import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Lift
import Language.Haskell.TH
#if __GLASGOW_HASKELL__ <= 708
import Data.Word
#endif

$(deriveLiftMany [ ''DExp, ''DPat, ''DType, ''DKind, ''DPred, ''DTyVarBndr
                 , ''DMatch, ''DClause, ''DLetDec, ''DDec, ''DCon
                 , ''DConFields, ''DForeign, ''DPragma, ''DRuleBndr, ''DTySynEqn
                 , ''NewOrData
                 , ''Lit, ''TyLit, ''Fixity, ''FixityDirection, ''Strict
                 , ''Callconv, ''Safety, ''Inline, ''RuleMatch, ''Phases
                 , ''AnnTarget, ''FunDep, ''FamFlavour, ''Role ])

#if __GLASGOW_HASKELL__ <= 708
-- Other type liftings:
                                      
instance Lift Word8 where
  lift word = return $ (VarE 'fromInteger) `AppE` (LitE $ IntegerL (toInteger word))
#endif
