{- Language/Haskell/TH/Desugar/Sweeten.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Converts desugared TH back into real TH.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskellQuotes #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Sweeten
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
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
  patSynDirToTH,
#endif

  typeArgToTH
  ) where

import Prelude hiding (exp)
import Control.Arrow

import Language.Haskell.TH hiding (Extension(..), cxt)
import Language.Haskell.TH.Datatype.TyVarBndr

import Language.Haskell.TH.Desugar.AST
import Language.Haskell.TH.Desugar.Core (DTypeArg(..))
import Language.Haskell.TH.Desugar.Util

expToTH :: DExp -> Exp
expToTH (DVarE n)            = VarE n
expToTH (DConE n)            = ConE n
expToTH (DLitE l)            = LitE l
expToTH (DAppE e1 e2)        = AppE (expToTH e1) (expToTH e2)
expToTH (DLamE names exp)    = LamE (map VarP names) (expToTH exp)
expToTH (DCaseE exp matches) = CaseE (expToTH exp) (map matchToTH matches)
expToTH (DLetE decs exp)     = LetE (map letDecToTH decs) (expToTH exp)
expToTH (DSigE exp ty)       = SigE (expToTH exp) (typeToTH ty)
expToTH (DStaticE exp)       = StaticE (expToTH exp)
#if __GLASGOW_HASKELL__ >= 801
expToTH (DAppTypeE exp ty)   = AppTypeE (expToTH exp) (typeToTH ty)
#else
-- In the event that we're on a version of Template Haskell without support for
-- type applications, we will simply drop the applied type.
expToTH (DAppTypeE exp _)    = expToTH exp
#endif
#if __GLASGOW_HASKELL__ >= 907
expToTH (DTypedBracketE exp) = TypedBracketE (expToTH exp)
expToTH (DTypedSpliceE exp)  = TypedSpliceE (expToTH exp)
#else
expToTH (DTypedBracketE {})  =
  error "Typed Template Haskell brackets supported only in GHC 9.8+"
expToTH (DTypedSpliceE {})   =
  error "Typed Template Haskell splices supported only in GHC 9.8+"
#endif

matchToTH :: DMatch -> Match
matchToTH (DMatch pat exp) = Match (patToTH pat) (NormalB (expToTH exp)) []

patToTH :: DPat -> Pat
patToTH (DLitP lit)         = LitP lit
patToTH (DVarP n)           = VarP n
patToTH (DConP n _tys pats) = ConP n
#if __GLASGOW_HASKELL__ >= 901
                                   (map typeToTH _tys)
#endif
                                   (map patToTH pats)
patToTH (DTildeP pat)       = TildeP (patToTH pat)
patToTH (DBangP pat)        = BangP (patToTH pat)
patToTH (DSigP pat ty)      = SigP (patToTH pat) (typeToTH ty)
patToTH DWildP              = WildP

decsToTH :: [DDec] -> [Dec]
decsToTH = map decToTH

-- | This returns a list of @Dec@s because GHC 7.6.3 does not have
-- a one-to-one mapping between 'DDec' and @Dec@.
decToTH :: DDec -> Dec
decToTH (DLetDec d) = letDecToTH d
decToTH (DDataD Data cxt n tvbs _mk cons derivings) =
  DataD (cxtToTH cxt) n (map tvbToTH tvbs) (fmap typeToTH _mk) (map conToTH cons)
        (concatMap derivClauseToTH derivings)
decToTH (DDataD Newtype cxt n tvbs _mk [con] derivings) =
  NewtypeD (cxtToTH cxt) n (map tvbToTH tvbs) (fmap typeToTH _mk) (conToTH con)
           (concatMap derivClauseToTH derivings)
decToTH (DDataD Newtype _cxt _n _tvbs _mk _cons _derivings) =
  error "Newtype declaration without exactly 1 constructor."
decToTH (DTySynD n tvbs ty) = TySynD n (map tvbToTH tvbs) (typeToTH ty)
decToTH (DClassD cxt n tvbs fds decs) =
  ClassD (cxtToTH cxt) n (map tvbToTH tvbs) fds (decsToTH decs)
decToTH (DInstanceD over _mtvbs cxt ty decs) =
  -- We deliberately avoid sweetening _mtvbs. See #151.
  instanceDToTH over cxt ty decs
decToTH (DForeignD f) = ForeignD (foreignToTH f)
decToTH (DOpenTypeFamilyD (DTypeFamilyHead n tvbs frs ann)) =
  OpenTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)
decToTH (DDataFamilyD n tvbs mk) =
  DataFamilyD n (map tvbToTH tvbs) (fmap typeToTH mk)
decToTH (DDataInstD nd cxt mtvbs lhs mk cons derivings) =
  let ndc = case (nd, cons) of
              (Newtype,  [con]) -> DNewtypeCon con
              (Newtype,  _)     -> error "Newtype that doesn't have only one constructor"
              (Data,     _)     -> DDataCons cons
              (TypeData, _)     -> error "Data family instance that is combined with `type data`"
  in dataInstDecToTH ndc cxt mtvbs lhs mk derivings
#if __GLASGOW_HASKELL__ >= 807
decToTH (DTySynInstD eqn) = TySynInstD (snd $ tySynEqnToTH eqn)
#else
decToTH (DTySynInstD eqn) =
  let (n, eqn') = tySynEqnToTH eqn in
  TySynInstD n eqn'
#endif
decToTH (DClosedTypeFamilyD (DTypeFamilyHead n tvbs frs ann) eqns) =
  ClosedTypeFamilyD (TypeFamilyHead n (map tvbToTH tvbs) (frsToTH frs) ann)
                    (map (snd . tySynEqnToTH) eqns)
decToTH (DRoleAnnotD n roles) = RoleAnnotD n roles
decToTH (DStandaloneDerivD mds _mtvbs cxt ty) =
  -- We deliberately avoid sweetening _mtvbs. See #151.
  standaloneDerivDToTH mds cxt ty
decToTH (DDefaultSigD n ty)        = DefaultSigD n (typeToTH ty)
#if __GLASGOW_HASKELL__ >= 801
decToTH (DPatSynD n args dir pat) = PatSynD n args (patSynDirToTH dir) (patToTH pat)
decToTH (DPatSynSigD n ty)        = PatSynSigD n (typeToTH ty)
#else
decToTH DPatSynD{}    = patSynErr
decToTH DPatSynSigD{} = patSynErr
#endif
#if __GLASGOW_HASKELL__ >= 809
decToTH (DKiSigD n ki) = KiSigD n (typeToTH ki)
#else
decToTH (DKiSigD {})   =
  error "Standalone kind signatures supported only in GHC 8.10+"
#endif
#if __GLASGOW_HASKELL__ >= 903
decToTH (DDefaultD tys) = DefaultD (map typeToTH tys)
#else
decToTH (DDefaultD{})   =
  error "Default declarations supported only in GHC 9.4+"
#endif
#if __GLASGOW_HASKELL__ >= 906
decToTH (DDataD TypeData _cxt n tvbs mk cons _derivings) =
  -- NB: Due to the invariants on 'DDataD' and 'TypeData', _cxt and _derivings
  -- will be empty.
  TypeDataD n (map tvbToTH tvbs) (fmap typeToTH mk) (map conToTH cons)
#else
decToTH (DDataD TypeData _cxt _n _tvbs _mk _cons _derivings) =
  error "`type data` declarations supported only in GHC 9.6+"
#endif

#if __GLASGOW_HASKELL__ < 801
patSynErr :: a
patSynErr = error "Pattern synonyms supported only in GHC 8.2+"
#endif

-- | Indicates whether something is a newtype or data type, bundling its
-- constructor(s) along with it.
data DNewOrDataCons
  = DNewtypeCon DCon
  | DDataCons   [DCon]

-- | Sweeten a 'DDataInstD'.
dataInstDecToTH :: DNewOrDataCons -> DCxt -> Maybe [DTyVarBndrUnit] -> DType
                -> Maybe DKind -> [DDerivClause] -> Dec
dataInstDecToTH ndc cxt _mtvbs lhs _mk derivings =
  case ndc of
    DNewtypeCon con ->
#if __GLASGOW_HASKELL__ >= 807
      NewtypeInstD (cxtToTH cxt) (fmap (fmap tvbToTH) _mtvbs) (typeToTH lhs)
                   (fmap typeToTH _mk) (conToTH con)
                   (concatMap derivClauseToTH derivings)
#else
      NewtypeInstD (cxtToTH cxt) _n _lhs_args (fmap typeToTH _mk) (conToTH con)
                   (concatMap derivClauseToTH derivings)
#endif

    DDataCons cons ->
#if __GLASGOW_HASKELL__ >= 807
      DataInstD (cxtToTH cxt) (fmap (fmap tvbToTH) _mtvbs) (typeToTH lhs)
                (fmap typeToTH _mk) (map conToTH cons)
                (concatMap derivClauseToTH derivings)
#else
      DataInstD (cxtToTH cxt) _n _lhs_args (fmap typeToTH _mk) (map conToTH cons)
                (concatMap derivClauseToTH derivings)
#endif
  where
    _lhs' = typeToTH lhs
    (_n, _lhs_args) =
      case unfoldType _lhs' of
        (ConT n, lhs_args) -> (n, filterTANormals lhs_args)
        (_, _) -> error $ "Illegal data instance LHS: " ++ pprint _lhs'

frsToTH :: DFamilyResultSig -> FamilyResultSig
frsToTH DNoSig          = NoSig
frsToTH (DKindSig k)    = KindSig (typeToTH k)
frsToTH (DTyVarSig tvb) = TyVarSig (tvbToTH tvb)

-- | Sweeten a 'DLetDec'.
letDecToTH :: DLetDec -> Dec
letDecToTH (DFunD name clauses) = FunD name (map clauseToTH clauses)
letDecToTH (DValD pat exp)      = ValD (patToTH pat) (NormalB (expToTH exp)) []
letDecToTH (DSigD name ty)      = SigD name (typeToTH ty)
letDecToTH (DInfixD f _ns_spec name) =
  InfixD f
#if __GLASGOW_HASKELL__ >= 909
         _ns_spec
#endif
         name
letDecToTH (DPragmaD prag)      = PragmaD (pragmaToTH prag)

conToTH :: DCon -> Con
conToTH (DCon [] [] n (DNormalC _ stys) rty) =
  GadtC [n] (map (second typeToTH) stys) (typeToTH rty)
conToTH (DCon [] [] n (DRecC vstys) rty) =
  RecGadtC [n] (map (thirdOf3 typeToTH) vstys) (typeToTH rty)
-- On GHC 8.0 or later, we sweeten every constructor to GADT syntax, so it is
-- perfectly OK to put all of the quantified type variables
-- (both universal and existential) in a ForallC.
conToTH (DCon tvbs cxt n fields rty) =
  ForallC (map tvbToTH tvbs) (cxtToTH cxt) (conToTH $ DCon [] [] n fields rty)

instanceDToTH :: Maybe Overlap -> DCxt -> DType -> [DDec] -> Dec
instanceDToTH over cxt ty decs =
  InstanceD over (cxtToTH cxt) (typeToTH ty) (decsToTH decs)

standaloneDerivDToTH :: Maybe DDerivStrategy -> DCxt -> DType -> Dec
standaloneDerivDToTH _mds cxt ty =
  StandaloneDerivD
#if __GLASGOW_HASKELL__ >= 802
                   (fmap derivStrategyToTH _mds)
#endif
                   (cxtToTH cxt) (typeToTH ty)

foreignToTH :: DForeign -> Foreign
foreignToTH (DImportF cc safety str n ty) =
  ImportF cc safety str n (typeToTH ty)
foreignToTH (DExportF cc str n ty) = ExportF cc str n (typeToTH ty)

pragmaToTH :: DPragma -> Pragma
pragmaToTH (DInlineP n inl rm phases) = InlineP n inl rm phases
pragmaToTH (DSpecialiseP n ty m_inl phases) =
  SpecialiseP n (typeToTH ty) m_inl phases
pragmaToTH (DSpecialiseInstP ty) = SpecialiseInstP (typeToTH ty)
#if __GLASGOW_HASKELL__ >= 807
pragmaToTH (DRuleP str mtvbs rbs lhs rhs phases) =
  RuleP str (fmap (fmap tvbToTH) mtvbs) (map ruleBndrToTH rbs)
        (expToTH lhs) (expToTH rhs) phases
#else
pragmaToTH (DRuleP str _ rbs lhs rhs phases) =
  RuleP str (map ruleBndrToTH rbs) (expToTH lhs) (expToTH rhs) phases
#endif
pragmaToTH (DAnnP target exp) = AnnP target (expToTH exp)
pragmaToTH (DLineP n str) = LineP n str
#if __GLASGOW_HASKELL__ < 801
pragmaToTH (DCompleteP {}) = error "COMPLETE pragmas only supported in GHC 8.2+"
#else
pragmaToTH (DCompleteP cls mty) = CompleteP cls mty
#endif
#if __GLASGOW_HASKELL__ >= 903
pragmaToTH (DOpaqueP n) = OpaqueP n
#else
pragmaToTH (DOpaqueP {}) = error "OPAQUE pragmas only supported in GHC 9.4+"
#endif

ruleBndrToTH :: DRuleBndr -> RuleBndr
ruleBndrToTH (DRuleVar n) = RuleVar n
ruleBndrToTH (DTypedRuleVar n ty) = TypedRuleVar n (typeToTH ty)

#if __GLASGOW_HASKELL__ >= 807
-- | It's convenient to also return a 'Name' here, since some call sites make
-- use of it.
tySynEqnToTH :: DTySynEqn -> (Name, TySynEqn)
tySynEqnToTH (DTySynEqn tvbs lhs rhs) =
  let lhs' = typeToTH lhs in
  case unfoldType lhs' of
    (ConT n, _lhs_args) -> (n, TySynEqn (fmap (fmap tvbToTH) tvbs) lhs' (typeToTH rhs))
    (_, _) -> error $ "Illegal type instance LHS: " ++ pprint lhs'
#else
tySynEqnToTH :: DTySynEqn -> (Name, TySynEqn)
tySynEqnToTH (DTySynEqn _ lhs rhs) =
  let lhs' = typeToTH lhs in
  case unfoldType lhs' of
    (ConT n, lhs_args) -> (n, TySynEqn (filterTANormals lhs_args) (typeToTH rhs))
    (_, _) -> error $ "Illegal type instance LHS: " ++ pprint lhs'
#endif

clauseToTH :: DClause -> Clause
clauseToTH (DClause pats exp) = Clause (map patToTH pats) (NormalB (expToTH exp)) []

typeToTH :: DType -> Type
-- We need a special case for DForallT ForallInvis followed by DConstrainedT
-- so that we may collapse them into a single ForallT when sweetening.
-- See Note [Desugaring and sweetening ForallT] in L.H.T.Desugar.Core.
typeToTH (DForallT (DForallInvis tvbs) (DConstrainedT ctxt ty)) =
  ForallT (map tvbToTH tvbs) (map predToTH ctxt) (typeToTH ty)
typeToTH (DForallT tele ty) =
  case tele of
    DForallInvis  tvbs -> ForallT (map tvbToTH tvbs) [] ty'
    DForallVis   _tvbs ->
#if __GLASGOW_HASKELL__ >= 809
      ForallVisT (map tvbToTH _tvbs) ty'
#else
      error "Visible dependent quantification supported only in GHC 8.10+"
#endif
  where
    ty'   = typeToTH ty
typeToTH (DConstrainedT cxt ty) = ForallT [] (map predToTH cxt) (typeToTH ty)
typeToTH (DAppT t1 t2)          = AppT (typeToTH t1) (typeToTH t2)
typeToTH (DSigT ty ki)          = SigT (typeToTH ty) (typeToTH ki)
typeToTH (DVarT n)              = VarT n
typeToTH (DConT n)              = tyconToTH n
typeToTH DArrowT                = ArrowT
typeToTH (DLitT lit)            = LitT lit
typeToTH DWildCardT = WildCardT
#if __GLASGOW_HASKELL__ >= 807
typeToTH (DAppKindT t k)        = AppKindT (typeToTH t) (typeToTH k)
#else
-- In the event that we're on a version of Template Haskell without support for
-- kind applications, we will simply drop the applied kind.
typeToTH (DAppKindT t _)        = typeToTH t
#endif

tvbToTH :: DTyVarBndr flag -> TyVarBndr_ flag
tvbToTH (DPlainTV n flag)    = plainTVFlag n flag
tvbToTH (DKindedTV n flag k) = kindedTVFlag n flag (typeToTH k)

cxtToTH :: DCxt -> Cxt
cxtToTH = map predToTH

#if __GLASGOW_HASKELL__ >= 801
derivClauseToTH :: DDerivClause -> [DerivClause]
derivClauseToTH (DDerivClause mds cxt) =
  [DerivClause (fmap derivStrategyToTH mds) (cxtToTH cxt)]
#else
derivClauseToTH :: DDerivClause -> Cxt
derivClauseToTH (DDerivClause _ cxt) = cxtToTH cxt
#endif

#if __GLASGOW_HASKELL__ >= 801
derivStrategyToTH :: DDerivStrategy -> DerivStrategy
derivStrategyToTH DStockStrategy    = StockStrategy
derivStrategyToTH DAnyclassStrategy = AnyclassStrategy
derivStrategyToTH DNewtypeStrategy  = NewtypeStrategy
#if __GLASGOW_HASKELL__ >= 805
derivStrategyToTH (DViaStrategy ty) = ViaStrategy (typeToTH ty)
#else
derivStrategyToTH (DViaStrategy _)  = error "DerivingVia supported only in GHC 8.6+"
#endif
#endif

#if __GLASGOW_HASKELL__ >= 801
patSynDirToTH :: DPatSynDir -> PatSynDir
patSynDirToTH DUnidir              = Unidir
patSynDirToTH DImplBidir           = ImplBidir
patSynDirToTH (DExplBidir clauses) = ExplBidir (map clauseToTH clauses)
#endif

predToTH :: DPred -> Pred
predToTH (DAppT p t) = AppT (predToTH p) (typeToTH t)
predToTH (DSigT p k) = SigT (predToTH p) (typeToTH k)
predToTH (DVarT n)   = VarT n
predToTH (DConT n)   = typeToTH (DConT n)
predToTH DArrowT     = ArrowT
predToTH (DLitT lit) = LitT lit
predToTH DWildCardT  = WildCardT
#if __GLASGOW_HASKELL__ >= 805
-- We need a special case for DForallT ForallInvis followed by DConstrainedT
-- so that we may collapse them into a single ForallT when sweetening.
-- See Note [Desugaring and sweetening ForallT] in L.H.T.Desugar.Core.
predToTH (DForallT (DForallInvis tvbs) (DConstrainedT ctxt p)) =
  ForallT (map tvbToTH tvbs) (map predToTH ctxt) (predToTH p)
predToTH (DForallT tele p) =
  case tele of
    DForallInvis tvbs -> ForallT (map tvbToTH tvbs) [] (predToTH p)
    DForallVis _      -> error "Visible dependent quantifier spotted at head of a constraint"
predToTH (DConstrainedT cxt p) = ForallT [] (map predToTH cxt) (predToTH p)
#else
predToTH (DForallT {})      = error "Quantified constraints supported only in GHC 8.6+"
predToTH (DConstrainedT {}) = error "Quantified constraints supported only in GHC 8.6+"
#endif
#if __GLASGOW_HASKELL__ >= 807
predToTH (DAppKindT p k) = AppKindT (predToTH p) (typeToTH k)
#else
-- In the event that we're on a version of Template Haskell without support for
-- kind applications, we will simply drop the applied kind.
predToTH (DAppKindT p _) = predToTH p
#endif

tyconToTH :: Name -> Type
tyconToTH n
  | n == ''(->)                 = ArrowT -- Work around Trac #14888
  | n == ''[]                   = ListT
  | n == ''(~)                  = EqualityT
  | n == '[]                    = PromotedNilT
  | n == '(:)                   = PromotedConsT
  | Just deg <- tupleNameDegree_maybe n
                                = if isDataName n
#if __GLASGOW_HASKELL__ >= 805
                                  then PromotedTupleT deg
#else
                                  then PromotedT n -- Work around Trac #14843
#endif
                                  else TupleT deg
  | Just deg <- unboxedTupleNameDegree_maybe n = UnboxedTupleT deg
#if __GLASGOW_HASKELL__ >= 801
  | Just deg <- unboxedSumNameDegree_maybe n   = UnboxedSumT deg
#endif
  | otherwise                   = ConT n

typeArgToTH :: DTypeArg -> TypeArg
typeArgToTH (DTANormal t) = TANormal (typeToTH t)
typeArgToTH (DTyArg k)    = TyArg    (typeToTH k)
