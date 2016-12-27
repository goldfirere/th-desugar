{- Language/Haskell/TH/Desugar.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             TypeSynonymInstances, FlexibleInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Desugars full Template Haskell syntax into a smaller core syntax for further
-- processing. The desugared types and constructors are prefixed with a D.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar (
  -- * Desugared data types
  DExp(..), DLetDec(..), DPat(..), DType(..), DKind, DCxt, DPred(..),
  DTyVarBndr(..), DMatch(..), DClause(..), DDec(..),
  DDerivClause(..), DerivStrategy(..), DPatSynDir(..),
  Overlap(..), PatSynArgs(..), NewOrData(..),
  DTypeFamilyHead(..), DFamilyResultSig(..), InjectivityAnn(..),
  DCon(..), DConFields(..), DBangType, DVarBangType,
  Bang(..), SourceUnpackedness(..), SourceStrictness(..),
  DForeign(..),
  DPragma(..), DRuleBndr(..), DTySynEqn(..), DInfo(..), DInstanceDec,
  Role(..), AnnTarget(..),

  -- * The 'Desugar' class
  Desugar(..),

  -- * Main desugaring functions
  dsExp, dsDecs, dsType, dsInfo,
  dsPatOverExp, dsPatsOverExp, dsPatX,
  dsLetDecs, dsTvb, dsCxt,
  dsCon, dsForeign, dsPragma, dsRuleBndr,

  -- ** Secondary desugaring functions
  PatM, dsPred, dsPat, dsDec, dsDerivClause, dsLetDec,
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses,
  dsBangType, dsVarBangType,
#if __GLASGOW_HASKELL__ > 710
  dsTypeFamilyHead, dsFamilyResultSig,
#endif
#if __GLASGOW_HASKELL__ >= 801
  dsPatSynDir,
#endif

  -- * Converting desugared AST back to TH AST
  module Language.Haskell.TH.Desugar.Sweeten,

  -- * Expanding type synonyms
  expand, expandType,

  -- * Reification
  reifyWithWarning,

  -- | The following definitions allow you to register a list of
  -- @Dec@s to be used in reification queries.
  withLocalDeclarations, dsReify, reifyWithLocals_maybe, reifyWithLocals,
  DsMonad(..), DsM,

  -- * Nested pattern flattening
  scExp, scLetDec,

  -- * Utility functions
  applyDExp, applyDType,
  dPatToDExp, removeWilds,
  getDataD, dataConNameToDataName, dataConNameToCon,
  nameOccursIn, allNamesIn, flattenDValD, getRecordSelectors,
  mkTypeName, mkDataName, newUniqueName,
  mkTupleDExp, mkTupleDPat, maybeDLetE, maybeDCaseE,
  substTy,
  tupleDegree_maybe, tupleNameDegree_maybe,
  unboxedSumDegree_maybe, unboxedSumNameDegree_maybe,
  unboxedTupleDegree_maybe, unboxedTupleNameDegree_maybe,
  strictToBang,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.Reify
import Language.Haskell.TH.Desugar.Expand
import Language.Haskell.TH.Desugar.Match

import qualified Data.Set as S
#if __GLASGOW_HASKELL__ < 709
import Data.Foldable ( foldMap )
#endif
import Prelude hiding ( exp )

-- | This class relates a TH type with its th-desugar type and allows
-- conversions back and forth. The functional dependency goes only one
-- way because `Type` and `Kind` are type synonyms, but they desugar
-- to different types.
class Desugar th ds | ds -> th where
  desugar :: DsMonad q => th -> q ds
  sweeten :: ds -> th

instance Desugar Exp DExp where
  desugar = dsExp
  sweeten = expToTH

instance Desugar Type DType where
  desugar = dsType
  sweeten = typeToTH

instance Desugar Cxt DCxt where
  desugar = dsCxt
  sweeten = cxtToTH

instance Desugar TyVarBndr DTyVarBndr where
  desugar = dsTvb
  sweeten = tvbToTH

instance Desugar [Dec] [DDec] where
  desugar = dsDecs
  sweeten = decsToTH

instance Desugar [Con] [DCon] where
  desugar = concatMapM dsCon
  sweeten = map conToTH

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
      y <- newUniqueName "y"
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
        DTildePa pa -> DTildePa (wildify name y pa)
        DBangPa pa -> DBangPa (wildify name y pa)
        DSigPa pa ty -> DSigPa (wildify name y pa) ty
        DWildPa -> DWildPa

flattenDValD other_dec = return [other_dec]

fvDType :: DType -> S.Set Name
fvDType = go
  where
    go (DForallT tvbs _cxt ty) = go ty `S.difference` (foldMap dtvbName tvbs)
    go (DAppT ty1 ty2)         = go ty1 `S.union` go ty2
    go (DSigT ty ki)           = go ty `S.union` fvDType ki
    go (DVarT n)               = S.singleton n
    go (DConT _)               = S.empty
    go DArrowT                 = S.empty
    go (DLitT {})              = S.empty
    go DWildCardT              = S.empty
    go DStarT                  = S.empty

dtvbName :: DTyVarBndr -> S.Set Name
dtvbName (DPlainTV n)    = S.singleton n
dtvbName (DKindedTV n _) = S.singleton n

-- | Produces 'DLetDec's representing the record selector functions from
-- the provided 'DCon'.
getRecordSelectors :: Quasi q
                   => DType        -- ^ the type of the argument
                   -> DCon
                   -> q [DLetDec]
getRecordSelectors arg_ty (DCon _ _ con_name con _) = case con of
    DRecC fields -> go fields
    _ -> return []
  where
    go fields = do
      varName <- qNewName "field"
      let tvbs = fvDType arg_ty
          maybe_forall
            | S.null tvbs = id
            | otherwise   = DForallT (map DPlainTV $ S.toList tvbs) []
          num_pats = length fields
      return $ concat
        [ [ DSigD name (maybe_forall $ DArrowT `DAppT` arg_ty `DAppT` res_ty)
          , DFunD name [DClause [DConPa con_name (mk_field_pats n num_pats varName)]
                                (DVarE varName)] ]
        | ((name, _strict, res_ty), n) <- zip fields [0..]
        , fvDType res_ty `S.isSubsetOf` tvbs   -- exclude "naughty" selectors
        ]

    mk_field_pats :: Int -> Int -> Name -> [DPat]
    mk_field_pats 0 total name = DVarPa name : (replicate (total-1) DWildPa)
    mk_field_pats n total name = DWildPa : mk_field_pats (n-1) (total-1) name
