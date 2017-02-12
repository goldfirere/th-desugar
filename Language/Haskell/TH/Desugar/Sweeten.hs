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
  letDecToTH, typeToTH,

  conToTH, foreignToTH, pragmaToTH, ruleBndrToTH,
  clauseToTH, tvbToTH, cxtToTH, predToTH, derivClauseToTH,
#if __GLASGOW_HASKELL__ >= 801
  patSynDirToTH
#endif
  ) where

import Prelude hiding (exp)
import Control.Arrow

import Language.Haskell.TH hiding (cxt)

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util

import Data.Maybe ( maybeToList, mapMaybe )

expToTH :: DExp -> Exp
expToTH (DVarE n)            = VarE n
expToTH (DConE n)            = ConE n
expToTH (DLitE l)            = LitE l
expToTH (DAppE e1 e2)        = AppE (expToTH e1) (expToTH e2)
expToTH (DLamE names exp)    = LamE (map VarP names) (expToTH exp)
expToTH (DCaseE exp matches) = CaseE (expToTH exp) (map matchToTH matches)
expToTH (DLetE decs exp)     = case mapMaybe letDecToTH decs of
                                  -- This can only happen if we somehow have a DLetE containing only pragmas
                                  [] -> expToTH exp
                                  decs' -> LetE decs' (expToTH exp)
expToTH (DSigE exp ty)       = SigE (expToTH exp) (typeToTH ty)
#if __GLASGOW_HASKELL__ < 709
expToTH (DStaticE _)         = error "Static expressions supported only in GHC 7.10+"
#else
expToTH (DStaticE exp)       = StaticE (expToTH exp)
#endif
#if __GLASGOW_HASKELL__ >= 801
expToTH (DAppTypeE exp ty)   = AppTypeE (expToTH exp) (typeToTH ty)
#else
-- In the event that we're on a version of Template Haskell without support for
-- type applications, we will simply drop the applied type.
expToTH (DAppTypeE exp _)    = expToTH exp
#endif

matchToTH :: DMatch -> Match
matchToTH (DMatch pat exp) = Match (patToTH pat) (NormalB (expToTH exp)) []

patToTH :: DPat -> Pat
patToTH (DLitPa lit)    = LitP lit
patToTH (DVarPa n)      = VarP n
patToTH (DConPa n pats) = ConP n (map patToTH pats)
patToTH (DTildePa pat)  = TildeP (patToTH pat)
patToTH (DBangPa pat)   = BangP (patToTH pat)
patToTH (DSigPa pat ty) = SigP (patToTH pat) (typeToTH ty)
patToTH DWildPa         = WildP

decsToTH :: [DDec] -> [Dec]
decsToTH = concatMap decToTH

-- | This returns a list of @Dec@s because GHC 7.6.3 does not have
-- a one-to-one mapping between 'DDec' and @Dec@.
decToTH :: DDec -> [Dec]
decToTH (DLetDec d) = maybeToList (letDecToTH d)
decToTH (DDataD Data cxt n tvbs cons derivings) =
#if __GLASGOW_HASKELL__ > 710
  [DataD (cxtToTH cxt) n (map tvbToTH tvbs) Nothing (map conToTH cons)
         (concatMap derivClauseToTH derivings)]
#else
  [DataD (cxtToTH cxt) n (map tvbToTH tvbs) (map conToTH cons)
         (map derivingToTH derivings)]
#endif
decToTH (DDataD Newtype cxt n tvbs [con] derivings) =
#if __GLASGOW_HASKELL__ > 710
  [NewtypeD (cxtToTH cxt) n (map tvbToTH tvbs) Nothing (conToTH con)
            (concatMap derivClauseToTH derivings)]
#else
  [NewtypeD (cxtToTH cxt) n (map tvbToTH tvbs) (conToTH con)
            (map derivingToTH derivings)]
#endif
decToTH (DTySynD n tvbs ty) = [TySynD n (map tvbToTH tvbs) (typeToTH ty)]
decToTH (DClassD cxt n tvbs fds decs) =
  [ClassD (cxtToTH cxt) n (map tvbToTH tvbs) fds (decsToTH decs)]
#if __GLASGOW_HASKELL__ >= 711
decToTH (DInstanceD over cxt ty decs) =
  [InstanceD over (cxtToTH cxt) (typeToTH ty) (decsToTH decs)]
#else
decToTH (DInstanceD _ cxt ty decs) =
  [InstanceD (cxtToTH cxt) (typeToTH ty) (decsToTH decs)]
#endif
decToTH (DForeignD f) = [ForeignD (foreignToTH f)]
#if __GLASGOW_HASKELL__ > 710
decToTH (DOpenTypeFamilyD (DTypeFamilyHead n tvbs frs ann)) =
  [OpenTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)]
#else
decToTH (DOpenTypeFamilyD (DTypeFamilyHead n tvbs frs _ann)) =
  [FamilyD TypeFam n (map tvbToTH tvbs) (frsToTH frs)]
#endif
decToTH (DDataFamilyD n tvbs) =
#if __GLASGOW_HASKELL__ > 710
  [DataFamilyD n (map tvbToTH tvbs) Nothing]
#else
  [FamilyD DataFam n (map tvbToTH tvbs) Nothing]
#endif
decToTH (DDataInstD Data cxt n tys cons derivings) =
#if __GLASGOW_HASKELL__ > 710
  [DataInstD (cxtToTH cxt) n (map typeToTH tys) Nothing (map conToTH cons)
             (concatMap derivClauseToTH derivings)]
#else
  [DataInstD (cxtToTH cxt) n (map typeToTH tys) (map conToTH cons)
             (map derivingToTH derivings)]
#endif
decToTH (DDataInstD Newtype cxt n tys [con] derivings) =
#if __GLASGOW_HASKELL__ > 710
  [NewtypeInstD (cxtToTH cxt) n (map typeToTH tys) Nothing (conToTH con)
                (concatMap derivClauseToTH derivings)]
#else
  [NewtypeInstD (cxtToTH cxt) n (map typeToTH tys) (conToTH con)
                (map derivingToTH derivings)]
#endif
#if __GLASGOW_HASKELL__ < 707
decToTH (DTySynInstD n eqn) = [tySynEqnToTHDec n eqn]
decToTH (DClosedTypeFamilyD (DTypeFamilyHead n tvbs frs _ann) eqns) =
  (FamilyD TypeFam n (map tvbToTH tvbs) (frsToTH frs)) :
  (map (tySynEqnToTHDec n) eqns)
decToTH (DRoleAnnotD {}) = []
#else
decToTH (DTySynInstD n eqn) = [TySynInstD n (tySynEqnToTH eqn)]
#if __GLASGOW_HASKELL__ > 710
decToTH (DClosedTypeFamilyD (DTypeFamilyHead n tvbs frs ann) eqns) =
  [ClosedTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)
                     (map tySynEqnToTH eqns)
  ]
#else
decToTH (DClosedTypeFamilyD (DTypeFamilyHead n tvbs frs _ann) eqns) =
  [ClosedTypeFamilyD n (map tvbToTH tvbs) (frsToTH frs) (map tySynEqnToTH eqns)]
#endif
decToTH (DRoleAnnotD n roles) = [RoleAnnotD n roles]
#endif
#if __GLASGOW_HASKELL__ < 709
decToTH (DStandaloneDerivD {}) =
  error "Standalone deriving supported only in GHC 7.10+"
decToTH (DDefaultSigD {})      =
  error "Default method signatures supported only in GHC 7.10+"
#else
decToTH (DStandaloneDerivD _mds cxt ty) =
  [StandaloneDerivD
#if __GLASGOW_HASKELL__ >= 801
    _mds
#endif
    (cxtToTH cxt) (typeToTH ty)]
decToTH (DDefaultSigD n ty)        = [DefaultSigD n (typeToTH ty)]
#endif
#if __GLASGOW_HASKELL__ >= 801
decToTH (DPatSynD n args dir pat) = [PatSynD n args (patSynDirToTH dir) (patToTH pat)]
decToTH (DPatSynSigD n ty)        = [PatSynSigD n (typeToTH ty)]
#else
decToTH dec
  | DPatSynD{}    <- dec = patSynErr
  | DPatSynSigD{} <- dec = patSynErr
  where
    patSynErr = error "Pattern synonyms supported only in GHC 8.2+"
#endif
decToTH _ = error "Newtype declaration without exactly 1 constructor."

#if __GLASGOW_HASKELL__ > 710
frsToTH :: DFamilyResultSig -> FamilyResultSig
frsToTH DNoSig          = NoSig
frsToTH (DKindSig k)    = KindSig (typeToTH k)
frsToTH (DTyVarSig tvb) = TyVarSig (tvbToTH tvb)
#else
frsToTH :: DFamilyResultSig -> Maybe Kind
frsToTH DNoSig                      = Nothing
frsToTH (DKindSig k)                = Just (typeToTH k)
frsToTH (DTyVarSig (DPlainTV _))    = Nothing
frsToTH (DTyVarSig (DKindedTV _ k)) = Just (typeToTH k)
#endif

#if __GLASGOW_HASKELL__ <= 710
derivingToTH :: DDerivClause -> Name
derivingToTH (DDerivClause _ [DConPr nm]) = nm
derivingToTH p =
  error ("Template Haskell in GHC < 8.0 only allows simple derivings: " ++ show p)
#endif

-- | Note: This can currently only return a 'Nothing' if the 'DLetDec' is a pragma which
-- is not supported by the GHC version being used.
letDecToTH :: DLetDec -> Maybe Dec
letDecToTH (DFunD name clauses) = Just $ FunD name (map clauseToTH clauses)
letDecToTH (DValD pat exp)      = Just $ ValD (patToTH pat) (NormalB (expToTH exp)) []
letDecToTH (DSigD name ty)      = Just $ SigD name (typeToTH ty)
letDecToTH (DInfixD f name)     = Just $ InfixD f name
letDecToTH (DPragmaD prag)      = fmap PragmaD (pragmaToTH prag)

conToTH :: DCon -> Con
#if __GLASGOW_HASKELL__ > 710
conToTH (DCon [] [] n (DNormalC stys) (Just rty)) =
  GadtC [n] (map (second typeToTH) stys) (typeToTH rty)
conToTH (DCon [] [] n (DRecC vstys) (Just rty)) =
  RecGadtC [n] (map (thirdOf3 typeToTH) vstys) (typeToTH rty)
#endif
conToTH (DCon [] [] n (DNormalC stys) _) =
#if __GLASGOW_HASKELL__ > 710
  NormalC n (map (second typeToTH) stys)
#else
  NormalC n (map (bangToStrict *** typeToTH) stys)
#endif
conToTH (DCon [] [] n (DRecC vstys) _) =
#if __GLASGOW_HASKELL__ > 710
  RecC n (map (thirdOf3 typeToTH) vstys)
#else
  RecC n (map (\(v,b,t) -> (v,bangToStrict b,typeToTH t)) vstys)
#endif
conToTH (DCon tvbs cxt n fields rty) =
  ForallC (map tvbToTH tvbs) (cxtToTH cxt) (conToTH $ DCon [] [] n fields rty)

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
#if __GLASGOW_HASKELL__ < 801
pragmaToTH (DCompleteP {}) = Nothing
#else
pragmaToTH (DCompleteP cls mty) = Just $ CompleteP cls mty
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
typeToTH (DSigT ty ki)          = SigT (typeToTH ty) (typeToTH ki)
typeToTH (DVarT n)              = VarT n
typeToTH (DConT n)              = tyconToTH n
typeToTH DArrowT                = ArrowT
typeToTH (DLitT lit)            = LitT lit
#if __GLASGOW_HASKELL__ > 710
typeToTH DWildCardT = WildCardT
#else
typeToTH DWildCardT = error "Wildcards supported only in GHC 8.0+"
#endif
typeToTH DStarT = StarT

tvbToTH :: DTyVarBndr -> TyVarBndr
tvbToTH (DPlainTV n)           = PlainTV n
tvbToTH (DKindedTV n k)        = KindedTV n (typeToTH k)

cxtToTH :: DCxt -> Cxt
cxtToTH = map predToTH

#if __GLASGOW_HASKELL__ >= 801
derivClauseToTH :: DDerivClause -> [DerivClause]
derivClauseToTH (DDerivClause mds cxt) = [DerivClause mds (cxtToTH cxt)]
#else
derivClauseToTH :: DDerivClause -> Cxt
derivClauseToTH (DDerivClause _ cxt) = cxtToTH cxt
#endif

#if __GLASGOW_HASKELL__ >= 801
patSynDirToTH :: DPatSynDir -> PatSynDir
patSynDirToTH DUnidir              = Unidir
patSynDirToTH DImplBidir           = ImplBidir
patSynDirToTH (DExplBidir clauses) = ExplBidir (map clauseToTH clauses)
#endif

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
    go _ DWildCardPr
      = error "Wildcards supported only in GHC 8.0+"
#else
predToTH (DAppPr p t) = AppT (predToTH p) (typeToTH t)
predToTH (DSigPr p k) = SigT (predToTH p) (typeToTH k)
predToTH (DVarPr n)   = VarT n
predToTH (DConPr n)   = typeToTH (DConT n)
#if __GLASGOW_HASKELL__ > 710
predToTH DWildCardPr  = WildCardT
#else
predToTH DWildCardPr  = error "Wildcards supported only in GHC 8.0+"
#endif
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
#if __GLASGOW_HASKELL__ >= 801
  | Just deg <- unboxedSumNameDegree_maybe n   = UnboxedSumT deg
#endif
  | otherwise                   = ConT n

#if __GLASGOW_HASKELL__ <= 710
-- | Convert a 'Bang' to a 'Strict'
bangToStrict :: Bang -> Strict
bangToStrict (Bang SourceUnpack _) = Unpacked
bangToStrict (Bang _ SourceStrict) = IsStrict
bangToStrict (Bang _ _)            = NotStrict
#endif
