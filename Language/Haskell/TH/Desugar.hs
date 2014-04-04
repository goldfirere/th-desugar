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
  DPragma(..), DRuleBndr(..), DTySynEqn(..), DInfo(..), DInstanceDec,
  Role(..), AnnTarget(..),

  -- * Main desugaring functions
  dsExp, dsDecs, dsType, dsKind, dsInfo,
  dsPatOverExp, dsPatsOverExp, dsPatX,
  dsLetDecs, dsTvb, dsCxt,
  dsCon, dsForeign, dsPragma, dsRuleBndr,

  -- ** Secondary desugaring functions
  PatM, dsPred, dsPat, dsDec, dsLetDec,
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses, 

  -- * Utility functions
  dPatToDExp, removeWilds, reifyWithWarning, getDataD, dataConNameToCon,
  nameOccursIn, allNamesIn, flattenDValD,
  mkTypeName, mkDataName, newUniqueName,
  mkTupleDExp, mkTupleDPat, maybeDLetE, maybeDCaseE,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Syntax

import qualified Data.Set as S
import Data.Foldable ( foldMap )
import Prelude hiding ( exp )

-- | If the declaration passed in is a 'DValD', creates new, equivalent
-- declarations such that the 'DPat' in all 'DValD's is just a plain
-- 'DVarPa'. Other declarations are passed through unchanged.
-- Note that the declarations that come out of this function are rather
-- less efficient than those that come in: they have many more pattern
-- matches.
flattenDValD :: Quasi q => DLetDec -> q [DLetDec]
flattenDValD dec@(DValD (DVarPa _) _) = return [dec]
flattenDValD (DValD pat exp) = do
  x <- newUniqueName "x" -- must use newUniqueName here because we might be top-level
  let top_val_d = DValD (DVarPa x) exp
      bound_names = S.elems $ extractBoundNamesDPat pat
  other_val_ds <- mapM (mk_val_d x) bound_names
  return $ top_val_d : other_val_ds
  where
    mk_val_d x name = do
      y <- qNewName "y"
      let pat'  = wildify name y pat
          match = DMatch pat' (DVarE y)
          cas   = DCaseE (DVarE x) [match]
      return $ DValD (DVarPa name) cas

    wildify name y p =
      case p of
        DLitPa lit -> DLitPa lit
        DVarPa n
          | n == name -> DVarPa y
          | otherwise -> DWildPa
        DConPa con ps -> DConPa con (map (wildify name y) ps)
        DTildePa p -> DTildePa (wildify name y p)
        DBangPa p -> DBangPa (wildify name y p)
        DWildPa -> DWildPa
        
flattenDValD other_dec = return [other_dec]

-- | Extract the names bound in a @DPat@
extractBoundNamesDPat :: DPat -> S.Set Name
extractBoundNamesDPat (DLitPa _)      = S.empty
extractBoundNamesDPat (DVarPa n)      = S.singleton n
extractBoundNamesDPat (DConPa _ pats) = foldMap extractBoundNamesDPat pats
extractBoundNamesDPat (DTildePa pat)  = extractBoundNamesDPat pat
extractBoundNamesDPat (DBangPa pat)   = extractBoundNamesDPat pat
extractBoundNamesDPat DWildPa         = S.empty
