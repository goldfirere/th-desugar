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
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Lift

$(deriveLiftMany [ ''DExp, ''DPat, ''DType, ''DPred, ''DTyVarBndr
                 , ''DMatch, ''DClause, ''DLetDec, ''DDec, ''DCon
                 , ''DConFields, ''DForeign, ''DPragma, ''DRuleBndr, ''DTySynEqn
                 , ''NewOrData
#if __GLASGOW_HASKELL__ < 707
                 , ''AnnTarget, ''Role
#endif
                 , ''DTypeFamilyHead,  ''DFamilyResultSig
#if __GLASGOW_HASKELL__ <= 710
                 , ''InjectivityAnn, ''Bang, ''SourceUnpackedness
                 , ''SourceStrictness, ''Overlap
#endif
                 ])
