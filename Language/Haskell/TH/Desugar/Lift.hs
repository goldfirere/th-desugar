-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Lift
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
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
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.TH.Desugar.Lift () where

import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Lift

$(deriveLiftMany [ ''DExp, ''DPat, ''DType, ''DForallTelescope, ''DTyVarBndr
                 , ''DMatch, ''DClause, ''DLetDec, ''DDec, ''DDerivClause, ''DCon
                 , ''DConFields, ''DForeign, ''DPragma, ''DRuleBndr, ''DTySynEqn
                 , ''DPatSynDir, ''DPatSynPat , ''NewOrData, ''DDerivStrategy
                 , ''DTypeFamilyHead,  ''DFamilyResultSig
#if __GLASGOW_HASKELL__ < 801
                 , ''PatSynArgs
#endif
#if __GLASGOW_HASKELL__ < 900
                 , ''Specificity
#endif

                 , ''TypeArg,   ''DTypeArg
                 , ''FunArgs,   ''DFunArgs
                 , ''VisFunArg, ''DVisFunArg
                 , ''ForallTelescope
                 ])
