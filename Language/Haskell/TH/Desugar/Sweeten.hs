{- Language/Haskell/TH/Desugar/Sweeten.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Converts desugared TH back into real TH.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Sweeten
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- The functions in this module convert desugared Template Haskell back into
-- proper Template Haskell.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar.Sweeten (
  expToTH, matchToTH, patToTH, decsToTH, decToTH,
  letDecToTH, typeToTH, kindToTH,

  conToTH, foreignToTH, pragmaToTH, ruleBndrToTH,
  clauseToTH, tvbToTH, cxtToTH, predToTH
  ) where

import Prelude hiding (exp)
import Language.Haskell.TH hiding (cxt)

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util

import Data.Maybe ( maybeToList )

expToTH :: DExp -> Exp
expToTH (DVarE n)            = VarE n
expToTH (DConE n)            = ConE n
expToTH (DLitE l)            = LitE l
expToTH (DAppE e1 e2)        = AppE (expToTH e1) (expToTH e2)
expToTH (DLamE names exp)    = LamE (map VarP names) (expToTH exp)
expToTH (DCaseE exp matches) = CaseE (expToTH exp) (map matchToTH matches)
expToTH (DLetE decs exp)     = LetE (map letDecToTH decs) (expToTH exp)
expToTH (DSigE exp ty)       = SigE (expToTH exp) (typeToTH ty)
#if __GLASGOW_HASKELL__ < 709
expToTH (DStaticE _)         = error "Static expressions supported only in GHC 7.10+"
#else
expToTH (DStaticE exp)       = StaticE (expToTH exp)
#endif
#if __GLASGOW_HASKELL__ > 710
expToTH (DUnboundVarE n) = UnboundVarE n
#else
expToTH (DUnboundVarE _) = error "Wildcards supported only in GHC 8.0+"
#endif

matchToTH :: DMatch -> Match
matchToTH (DMatch pat exp) = Match (patToTH pat) (NormalB (expToTH exp)) []

patToTH :: DPat -> Pat
patToTH (DLitPa lit)    = LitP lit
patToTH (DVarPa n)      = VarP n
patToTH (DConPa n pats) = ConP n (map patToTH pats)
patToTH (DTildePa pat)  = TildeP (patToTH pat)
patToTH (DBangPa pat)   = BangP (patToTH pat)
patToTH DWildPa         = WildP

decsToTH :: [DDec] -> [Dec]
decsToTH = concatMap decToTH

-- | This returns a list of @Dec@s because GHC 7.6.3 does not have
-- a one-to-one mapping between 'DDec' and @Dec@.
decToTH :: DDec -> [Dec]
decToTH (DLetDec d) = [letDecToTH d]
decToTH (DDataD Data cxt n tvbs cons derivings) =
  [DataD (cxtToTH cxt) n (map tvbToTH tvbs) (map conToTH cons) derivings]
decToTH (DDataD Newtype cxt n tvbs [con] derivings) =
  [NewtypeD (cxtToTH cxt) n (map tvbToTH tvbs) (conToTH con) derivings]
decToTH (DTySynD n tvbs ty) = [TySynD n (map tvbToTH tvbs) (typeToTH ty)]
decToTH (DClassD cxt n tvbs fds decs) =
  [ClassD (cxtToTH cxt) n (map tvbToTH tvbs) fds (decsToTH decs)]
decToTH (DInstanceD cxt ty decs) =
  [InstanceD (cxtToTH cxt) (typeToTH ty) (decsToTH decs)]
decToTH (DForeignD f) = [ForeignD (foreignToTH f)]
decToTH (DPragmaD prag) = maybeToList $ fmap PragmaD (pragmaToTH prag)
#if __GLASGOW_HASKELL__ > 710
decToTH (DOpenTypeFamilyD n tvbs frs ann) =
  [OpenTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)]
decToTH (DDataFamilyD n tvbs m_k) =
  [DataFamilyD n (map tvbToTH tvbs) (fmap kindToTH m_k)]
#else
decToTH (DFamilyD flav n tvbs m_k) =
  [FamilyD flav n (map tvbToTH tvbs) (fmap kindToTH m_k)]
#endif
decToTH (DDataInstD Data cxt n tys cons derivings) =
  [DataInstD (cxtToTH cxt) n (map typeToTH tys) (map conToTH cons) derivings]
decToTH (DDataInstD Newtype cxt n tys [con] derivings) =
  [NewtypeInstD (cxtToTH cxt) n (map typeToTH tys) (conToTH con) derivings]
#if __GLASGOW_HASKELL__ < 707
decToTH (DTySynInstD n eqn) = [tySynEqnToTHDec n eqn]
decToTH (DClosedTypeFamilyD n tvbs m_k eqns) =
  (FamilyD TypeFam n (map tvbToTH tvbs) (fmap kindToTH m_k)) :
  (map (tySynEqnToTHDec n) eqns)
decToTH (DRoleAnnotD {}) = []
#else
decToTH (DTySynInstD n eqn) = [TySynInstD n (tySynEqnToTH eqn)]
#if __GLASGOW_HASKELL__ > 710
decToTH (DClosedTypeFamilyD n tvbs frs ann eqns) =
  [ClosedTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)
                       (map tySynEqnToTH eqns)]
#else
decToTH (DClosedTypeFamilyD n tvbs m_k eqns) =
  [ClosedTypeFamilyD n (map tvbToTH tvbs) (fmap kindToTH m_k)
                       (map tySynEqnToTH eqns)]
#endif
decToTH (DRoleAnnotD n roles) = [RoleAnnotD n roles]
#endif
#if __GLASGOW_HASKELL__ < 709
decToTH (DStandaloneDerivD {}) =
  error "Standalone deriving supported only in GHC 7.10+"
decToTH (DDefaultSigD {})      =
  error "Default method signatures supported only in GHC 7.10+"
#else
decToTH (DStandaloneDerivD cxt ty) =
  [StandaloneDerivD (cxtToTH cxt) (typeToTH ty)]
decToTH (DDefaultSigD n ty)        = [DefaultSigD n (typeToTH ty)]
#endif
decToTH _ = error "Newtype declaration without exactly 1 constructor."

#if __GLASGOW_HASKELL__ > 710
frsToTH :: DFamilyResultSig -> FamilyResultSig
frsToTH DNoSig = NoSig
frsToTH (DKindSig k) = KindSig (kindToTH k)
frsToTH (DTyVarSig tvb) = TyVarSig (tvbToTH tvb)
#endif

letDecToTH :: DLetDec -> Dec
letDecToTH (DFunD name clauses) = FunD name (map clauseToTH clauses)
letDecToTH (DValD pat exp)      = ValD (patToTH pat) (NormalB (expToTH exp)) []
letDecToTH (DSigD name ty)      = SigD name (typeToTH ty)
letDecToTH (DInfixD f name)     = InfixD f name

conToTH :: DCon -> Con
conToTH (DCon [] [] n (DNormalC stys)) =
  NormalC n (map (liftSnd typeToTH) stys)
conToTH (DCon [] [] n (DRecC vstys)) =
  RecC n (map (liftThdOf3 typeToTH) vstys)
conToTH (DCon tvbs cxt n fields) =
  ForallC (map tvbToTH tvbs) (cxtToTH cxt) (conToTH $ DCon [] [] n fields)

foreignToTH :: DForeign -> Foreign
foreignToTH (DImportF cc safety str n ty) =
  ImportF cc safety str n (typeToTH ty)
foreignToTH (DExportF cc str n ty) = ExportF cc str n (typeToTH ty)

pragmaToTH :: DPragma -> Maybe Pragma
pragmaToTH (DInlineP n inl rm phases) = Just $ InlineP n inl rm phases
pragmaToTH (DSpecialiseP n ty m_inl phases) =
  Just $ SpecialiseP n (typeToTH ty) m_inl phases
pragmaToTH (DSpecialiseInstP ty) = Just $ SpecialiseInstP (typeToTH ty)
pragmaToTH (DRuleP str rbs lhs rhs phases) =
  Just $ RuleP str (map ruleBndrToTH rbs) (expToTH lhs) (expToTH rhs) phases
#if __GLASGOW_HASKELL__ < 707
pragmaToTH (DAnnP {}) = Nothing
#else
pragmaToTH (DAnnP target exp) = Just $ AnnP target (expToTH exp)
#endif
#if __GLASGOW_HASKELL__ < 709
pragmaToTH (DLineP {}) = Nothing
#else
pragmaToTH (DLineP n str) = Just $ LineP n str
#endif

ruleBndrToTH :: DRuleBndr -> RuleBndr
ruleBndrToTH (DRuleVar n) = RuleVar n
ruleBndrToTH (DTypedRuleVar n ty) = TypedRuleVar n (typeToTH ty)

#if __GLASGOW_HASKELL__ < 707
-- | GHC 7.6.3 doesn't have TySynEqn, so we sweeten to a Dec in GHC 7.6.3;
-- GHC 7.8+ does not use this function
tySynEqnToTHDec :: Name -> DTySynEqn -> Dec
tySynEqnToTHDec n (DTySynEqn lhs rhs) =
  TySynInstD n (map typeToTH lhs) (typeToTH rhs)
#else
tySynEqnToTH :: DTySynEqn -> TySynEqn
tySynEqnToTH (DTySynEqn lhs rhs) = TySynEqn (map typeToTH lhs) (typeToTH rhs)
#endif

clauseToTH :: DClause -> Clause
clauseToTH (DClause pats exp) = Clause (map patToTH pats) (NormalB (expToTH exp)) []

typeToTH :: DType -> Type
typeToTH (DForallT tvbs cxt ty) = ForallT (map tvbToTH tvbs) (map predToTH cxt) (typeToTH ty)
typeToTH (DAppT t1 t2)          = AppT (typeToTH t1) (typeToTH t2)
typeToTH (DSigT ty ki)          = SigT (typeToTH ty) (kindToTH ki)
typeToTH (DVarT n)              = VarT n
typeToTH (DConT n)              = tyconToTH n
typeToTH DArrowT                = ArrowT
typeToTH (DLitT lit)            = LitT lit
#if __GLASGOW_HASKELL__ > 710
typeToTH (DWildCardT n) = WildCardT n
#else
typeToTH (DWildCardT _) = error "Wildcards supported only in GHC 8.0+"
#endif

tvbToTH :: DTyVarBndr -> TyVarBndr
tvbToTH (DPlainTV n)           = PlainTV n
tvbToTH (DKindedTV n k)        = KindedTV n (kindToTH k)

cxtToTH :: DCxt -> Cxt
cxtToTH = map predToTH

predToTH :: DPred -> Pred
#if __GLASGOW_HASKELL__ < 709
predToTH = go []
  where
    go acc (DAppPr p t) = go (typeToTH t : acc) p
    go acc (DSigPr p _) = go acc                p  -- this shouldn't happen.
    go _   (DVarPr _)
      = error "Template Haskell in GHC <= 7.8 does not support variable constraints."
    go acc (DConPr n) 
      | nameBase n == "~"
      , [t1, t2] <- acc
      = EqualP t1 t2
      | otherwise
      = ClassP n acc
    go _ (DWildCardPr _)
      = error "Wildcards supported only in GHC 8.0+"
#else
predToTH (DAppPr p t) = AppT (predToTH p) (typeToTH t)
predToTH (DSigPr p k) = SigT (predToTH p) (kindToTH k)
predToTH (DVarPr n)   = VarT n
predToTH (DConPr n)   = typeToTH (DConT n)
#if __GLASGOW_HASKELL__ > 710
predToTH (DWildCardPr n) = WildCardT n
#else
predToTH (DWildCardPr _) = error "Wildcards supported only in GHC 8.0+"
#endif
#endif

kindToTH :: DKind -> Kind
kindToTH (DForallK names ki) = ForallT (map PlainTV names) [] (kindToTH ki)
kindToTH (DVarK n)           = VarT n
kindToTH (DConK n kis)       = foldl AppT (tyconToTH n) (map kindToTH kis)
kindToTH (DArrowK k1 k2)     = AppT (AppT ArrowT (kindToTH k1)) (kindToTH k2)
kindToTH DStarK              = StarT
#if __GLASGOW_HASKELL__ > 710
kindToTH (DWildCardK n) = WildCardT n
#else
kindToTH (DWildCardK _) = error "Wildcards supported only in GHC 8.0+"
#endif

tyconToTH :: Name -> Type
tyconToTH n
  | n == ''[]                   = ListT
#if __GLASGOW_HASKELL__ >= 709
  | n == ''(~)                  = EqualityT
#endif
  | n == '[]                    = PromotedNilT
  | n == '(:)                   = PromotedConsT
  | Just deg <- tupleNameDegree_maybe n        = if isDataName n
                                                 then PromotedTupleT deg
                                                 else TupleT deg
  | Just deg <- unboxedTupleNameDegree_maybe n = UnboxedTupleT deg
  | otherwise                   = ConT n
