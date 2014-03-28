{- Language/Haskell/TH/Desugar.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE CPP #-}

{-|
Desugars full Template Haskell syntax into a smaller core syntax for further
processing. The desugared types and constructors are prefixed with a D.
-}

module Language.Haskell.TH.Desugar (
  -- * Desugared data types
  DExp(..), DLetDec(..), DPat(..), DType(..), DKind(..), DCxt, DPred(..),
  DTyVarBndr(..), DMatch(..), DClause(..), DDec(..), NewOrData(..),
  DCon(..), DConFields(..), DStrictType, DVarStrictType, DForeign(..),
  DPragma(..), DRuleBndr(..), DTySynEqn(..),
  Role(..), AnnTarget(..),

  -- * Main desugaring functions
  dsExp, dsPatOverExp, dsPatsOverExp, dsPatX,
  dsDecs, dsLetDecs, dsType, dsKind, dsTvb, dsCxt,
  dsCon, dsForeign, dsPragma, dsRuleBndr,

  -- ** Secondary desugaring functions
  PatM, dsPred, dsPat, dsDec, dsLetDec,
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses, 

  -- * Utility functions
  dPatToDExp, removeWilds, reifyWithWarning, getDataD, dataConNameToCon,
  mkTupleDExp, mkTupleDPat, maybeDLetE, maybeDCaseE,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util

#if __GLASGOW_HASKELL__ >= 707
import Language.Haskell.TH ( Role(..), AnnTarget(..) )
#endif
