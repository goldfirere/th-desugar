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

{-# LANGUAGE TemplateHaskell, MagicHash, TypeSynonymInstances, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.Haskell.TH.Desugar.Lift () where

import Prelude hiding ( mod, words )
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Syntax
import Control.Applicative
import GHC.Exts
import GHC.Word

foldApp :: Exp -> [Exp] -> Exp
foldApp = foldl AppE
           
instance Lift DExp where
  lift (DVarE n)      = foldApp (ConE 'DVarE)  <$> sequence [lift n]
  lift (DConE n)      = foldApp (ConE 'DConE)  <$> sequence [lift n]
  lift (DLitE l)      = foldApp (ConE 'DLitE)  <$> sequence [lift l]
  lift (DAppE e1 e2)  = foldApp (ConE 'DAppE)  <$> sequence [lift e1, lift e2]
  lift (DLamE ns e)   = foldApp (ConE 'DLamE)  <$> sequence [lift ns, lift e]
  lift (DCaseE e ms)  = foldApp (ConE 'DCaseE) <$> sequence [lift e, lift ms]
  lift (DLetE decs e) = foldApp (ConE 'DLetE)  <$> sequence [lift decs, lift e]
  lift (DSigE e t)    = foldApp (ConE 'DSigE)  <$> sequence [lift e, lift t]

instance Lift DPat where
  lift (DLitPa l)    = foldApp (ConE 'DLitPa)   <$> sequence [lift l]
  lift (DVarPa n)    = foldApp (ConE 'DVarPa)   <$> sequence [lift n]
  lift (DConPa n ps) = foldApp (ConE 'DConPa)   <$> sequence [lift n, lift ps]
  lift (DTildePa p)  = foldApp (ConE 'DTildePa) <$> sequence [lift p]
  lift (DBangPa p)   = foldApp (ConE 'DBangPa)  <$> sequence [lift p]
  lift DWildPa       = return $ ConE 'DWildPa

instance Lift DType where
  lift (DForallT tvbs cxt t) =
    foldApp (ConE 'DForallT) <$> sequence [lift tvbs, lift cxt, lift t]
  lift (DAppT t1 t2) = foldApp (ConE 'DAppT) <$> sequence [lift t1, lift t2]
  lift (DSigT t k)   = foldApp (ConE 'DSigT) <$> sequence [lift t, lift k]
  lift (DVarT n)     = foldApp (ConE 'DVarT) <$> sequence [lift n]
  lift (DConT n)     = foldApp (ConE 'DConT) <$> sequence [lift n]
  lift DArrowT       = return $ ConE 'DArrowT
  lift (DLitT l)     = foldApp (ConE 'DLitT) <$> sequence [lift l]

instance Lift DKind where
  lift (DForallK ns k) = foldApp (ConE 'DForallK) <$> sequence [lift ns, lift k]
  lift (DVarK n)       = foldApp (ConE 'DVarK)    <$> sequence [lift n]
  lift (DConK n ks)    = foldApp (ConE 'DConK)    <$> sequence [lift n, lift ks]
  lift (DArrowK k1 k2) = foldApp (ConE 'DArrowK)  <$> sequence [lift k1, lift k2]
  lift DStarK          = return $ ConE 'DStarK

instance Lift DPred where
  lift (DAppPr p t) = foldApp (ConE 'DAppPr) <$> sequence [lift p, lift t]
  lift (DSigPr p k) = foldApp (ConE 'DSigPr) <$> sequence [lift p, lift k]
  lift (DVarPr n)   = foldApp (ConE 'DVarPr) <$> sequence [lift n]
  lift (DConPr n)   = foldApp (ConE 'DConPr) <$> sequence [lift n]

instance Lift DTyVarBndr where
  lift (DPlainTV n)    = foldApp (ConE 'DPlainTV)  <$> sequence [lift n]
  lift (DKindedTV n k) = foldApp (ConE 'DKindedTV) <$> sequence [lift n, lift k]

instance Lift DMatch where
  lift (DMatch p e) = foldApp (ConE 'DMatch) <$> sequence [lift p, lift e]

instance Lift DClause where
  lift (DClause ps e) = foldApp (ConE 'DClause) <$> sequence [lift ps, lift e]

instance Lift DLetDec where
  lift (DFunD n cs)  = foldApp (ConE 'DFunD)   <$> sequence [lift n, lift cs]
  lift (DValD p e)   = foldApp (ConE 'DValD)   <$> sequence [lift p, lift e]
  lift (DSigD n t)   = foldApp (ConE 'DSigD)   <$> sequence [lift n, lift t]
  lift (DInfixD f n) = foldApp (ConE 'DInfixD) <$> sequence [lift f, lift n]

instance Lift NewOrData where
  lift Newtype = return $ ConE 'Newtype
  lift Data    = return $ ConE 'Data

instance Lift DDec where
  lift (DLetDec dec) = foldApp (ConE 'DLetDec) <$> sequence [lift dec]
  lift (DDataD nd cxt n tvbs cons derivs) =
    foldApp (ConE 'DDataD) <$> sequence [ lift nd, lift cxt, lift n
                                        , lift tvbs, lift cons, lift derivs ]
  lift (DTySynD n tvbs ty) =
    foldApp (ConE 'DTySynD) <$> sequence [lift n, lift tvbs, lift ty]
  lift (DClassD cxt n tvbs fds decs) =
    foldApp (ConE 'DClassD) <$> sequence [ lift cxt, lift n, lift tvbs
                                         , lift fds, lift decs ]
  lift (DInstanceD cxt ty decs) =
    foldApp (ConE 'DInstanceD) <$> sequence [lift cxt, lift ty, lift decs]
  lift (DForeignD for) = foldApp (ConE 'DForeignD) <$> sequence [lift for]
  lift (DPragmaD prag) = foldApp (ConE 'DPragmaD) <$> sequence [lift prag]
  lift (DFamilyD flav n tvbs res) =
    foldApp (ConE 'DFamilyD) <$> sequence [lift flav, lift n, lift tvbs, lift res]
  lift (DDataInstD nd cxt n tys cons derivs) =
    foldApp (ConE 'DDataInstD) <$> sequence [ lift nd, lift cxt, lift n
                                            , lift tys, lift cons, lift derivs ]
  lift (DTySynInstD n eqn) = foldApp (ConE 'DTySynInstD) <$> sequence [lift n, lift eqn]
  lift (DClosedTypeFamilyD n tvbs res eqns) =
    foldApp (ConE 'DClosedTypeFamilyD) <$> sequence [ lift n, lift tvbs
                                                    , lift res, lift eqns ]
  lift (DRoleAnnotD n rs) =
    foldApp (ConE 'DRoleAnnotD) <$> sequence [lift n, lift rs]

instance Lift DCon where
  lift (DCon tvbs cxt n fields) =
    foldApp (ConE 'DCon) <$> sequence [lift tvbs, lift cxt, lift n, lift fields]

instance Lift DConFields where
  lift (DNormalC stys) = foldApp (ConE 'DNormalC) <$> sequence [lift stys]
  lift (DRecC vstys)   = foldApp (ConE 'DRecC)    <$> sequence [lift vstys]

instance Lift DForeign where
  lift (DImportF cc safe str n ty) =
    foldApp (ConE 'DImportF) <$> sequence [ lift cc, lift safe, lift str
                                          , lift n, lift ty ]
  lift (DExportF cc str n ty) =
    foldApp (ConE 'DExportF) <$> sequence [lift cc, lift str, lift n, lift ty]

instance Lift DPragma where
  lift (DInlineP n i rm phases) =
    foldApp (ConE 'DInlineP) <$> sequence [lift n, lift i, lift rm, lift phases]
  lift (DSpecialiseP n ty m_i phases) =
    foldApp (ConE 'DSpecialiseP) <$> sequence [ lift n, lift ty
                                              , lift m_i, lift phases ]
  lift (DSpecialiseInstP ty) = foldApp (ConE 'DSpecialiseInstP) <$> sequence [lift ty]
  lift (DRuleP str bndrs e1 e2 phases) =
    foldApp (ConE 'DRuleP) <$> sequence [ lift str, lift bndrs, lift e1
                                        , lift e2, lift phases ]
  lift (DAnnP targ e) = foldApp (ConE 'DAnnP) <$> sequence [lift targ, lift e]

instance Lift DRuleBndr where
  lift (DRuleVar n) = foldApp (ConE 'DRuleVar) <$> sequence [lift n]
  lift (DTypedRuleVar n ty) =
    foldApp (ConE 'DTypedRuleVar) <$> sequence [lift n, lift ty]

instance Lift DTySynEqn where
  lift (DTySynEqn lhs rhs) = foldApp (ConE 'DTySynEqn) <$> sequence [lift lhs, lift rhs]
                                 
-- Template Haskell liftings

instance Lift OccName where
  lift (OccName n) = foldApp (ConE 'OccName) <$> sequence [lift n]

instance Lift ModName where
  lift (ModName n) = foldApp (ConE 'ModName) <$> sequence [lift n]

instance Lift PkgName where
  lift (PkgName n) = foldApp (ConE 'PkgName) <$> sequence [lift n]

instance Lift NameSpace where
  lift VarName   = return $ ConE 'VarName
  lift DataName  = return $ ConE 'DataName
  lift TcClsName = return $ ConE 'TcClsName

instance Lift NameFlavour where
  lift NameS       = return $ ConE 'NameS
  lift (NameQ mod) = foldApp (ConE 'NameQ) <$> sequence [lift mod]
  lift (NameU n)   = return $ foldApp (ConE 'NameU) [LitE $ IntPrimL $ toInteger $ I# n]
  lift (NameL n)   = return $ foldApp (ConE 'NameL) [LitE $ IntPrimL $ toInteger $ I# n]
  lift (NameG ns pkg mod) =
    foldApp (ConE 'NameG) <$> sequence [lift ns, lift pkg, lift mod]

instance Lift Name where
  lift (Name occ flav) = foldApp (ConE 'Name) <$> sequence [lift occ, lift flav]
                                  
instance Lift Lit where
  lift (CharL ch)          = foldApp (ConE 'CharL)       <$> sequence [lift ch]
  lift (StringL str)       = foldApp (ConE 'StringL)     <$> sequence [lift str]
  lift (IntegerL i)        = foldApp (ConE 'IntegerL)    <$> sequence [lift i]
  lift (RationalL rat)     = foldApp (ConE 'RationalL)   <$> sequence [lift rat]
  lift (IntPrimL i)        = foldApp (ConE 'IntPrimL)    <$> sequence [lift i]
  lift (WordPrimL i)       = foldApp (ConE 'WordPrimL)   <$> sequence [lift i]
  lift (FloatPrimL rat)    = foldApp (ConE 'FloatPrimL)  <$> sequence [lift rat]
  lift (DoublePrimL rat)   = foldApp (ConE 'DoublePrimL) <$> sequence [lift rat]
  lift (StringPrimL words) = foldApp (ConE 'StringPrimL) <$> sequence [lift words]

instance Lift TyLit where
  lift (NumTyLit i) = foldApp (ConE 'NumTyLit) <$> sequence [lift i]
  lift (StrTyLit s) = foldApp (ConE 'StrTyLit) <$> sequence [lift s]

instance Lift Fixity where
  lift (Fixity i dir) = foldApp (ConE 'Fixity) <$> sequence [lift i, lift dir]

instance Lift FixityDirection where
  lift InfixL = return $ ConE 'InfixL
  lift InfixR = return $ ConE 'InfixR
  lift InfixN = return $ ConE 'InfixN

instance Lift Strict where
  lift IsStrict  = return $ ConE 'IsStrict
  lift NotStrict = return $ ConE 'NotStrict
  lift Unpacked  = return $ ConE 'Unpacked

instance Lift Callconv where
  lift CCall   = return $ ConE 'CCall
  lift StdCall = return $ ConE 'StdCall

instance Lift Safety where
  lift Unsafe = return $ ConE 'Unsafe
  lift Safe   = return $ ConE 'Safe
  lift Interruptible = return $ ConE 'Interruptible

instance Lift Inline where
  lift NoInline  = return $ ConE 'NoInline
  lift Inline    = return $ ConE 'Inline
  lift Inlinable = return $ ConE 'Inlinable

instance Lift RuleMatch where
  lift ConLike = return $ ConE 'ConLike
  lift FunLike = return $ ConE 'FunLike

instance Lift Phases where
  lift AllPhases       = return $ ConE 'AllPhases
  lift (FromPhase i)   = foldApp (ConE 'FromPhase)   <$> sequence [lift i]
  lift (BeforePhase i) = foldApp (ConE 'BeforePhase) <$> sequence [lift i]

instance Lift AnnTarget where
  lift ModuleAnnotation    = return $ ConE 'ModuleAnnotation
  lift (TypeAnnotation n)  = foldApp (ConE 'TypeAnnotation)  <$> sequence [lift n]
  lift (ValueAnnotation n) = foldApp (ConE 'ValueAnnotation) <$> sequence [lift n]

instance Lift FunDep where
  lift (FunDep lhs rhs) = foldApp (ConE 'FunDep) <$> sequence [lift lhs, lift rhs]

instance Lift FamFlavour where
  lift TypeFam = return $ ConE 'TypeFam
  lift DataFam = return $ ConE 'DataFam

instance Lift Role where
  lift NominalR          = return $ ConE 'NominalR
  lift RepresentationalR = return $ ConE 'RepresentationalR
  lift PhantomR          = return $ ConE 'PhantomR
  lift InferR            = return $ ConE 'InferR

-- Other type liftings:
                                      
instance Lift Rational where
  lift rat = return $ LitE $ RationalL rat

instance Lift Word8 where
  lift word = return $ foldApp (VarE 'fromInteger) [LitE $ IntegerL (toInteger word)]
