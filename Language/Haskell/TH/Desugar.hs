{- Language/Haskell/TH/Desugar.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-|
Desugars full Template Haskell syntax into a smaller core syntax for further
processing. The desugared types and constructors are prefixed with a D.
-}

module Language.Haskell.TH.Desugar (
  -- * Desugared data types
  DExp(..), DLetDec(..), DPat(..), DType(..), DKind(..), DCxt, DPred(..),
  DTyVarBndr(..), DMatch(..), DClause(..),

  -- * Main desugaring functions
  dsExp, dsPat, dsPats, dsLetDec, dsType, dsKind, dsTvb, dsPred,

  -- ** Secondary desugaring functions
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses, 

  -- * Utility functions
  dPatToDExp, removeWilds, reifyWithWarning, getDataD, dataConNameToCon,
  mkTupleDExp, mkTupleDPat,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util