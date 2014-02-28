{- Language/Haskell/TH/Desugar/Sweeten.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Converts desugared TH back into real TH.
-}

{-# LANGUAGE CPP #-}

{-| The functions in this module convert desugared Template Haskell back into
    proper Template Haskell. -}

module Language.Haskell.TH.Desugar.Sweeten where

import Prelude hiding (exp)
import Language.Haskell.TH hiding (cxt)

import Language.Haskell.TH.Desugar.Core

expToTH :: DExp -> Exp
expToTH (DVarE n)            = VarE n
expToTH (DConE n)            = ConE n
expToTH (DLitE l)            = LitE l
expToTH (DAppE e1 e2)        = AppE (expToTH e1) (expToTH e2)
expToTH (DLamE names exp)    = LamE (map VarP names) (expToTH exp)
expToTH (DCaseE exp matches) = CaseE (expToTH exp) (map matchToTH matches)
expToTH (DLetE decs exp)     = LetE (map letDecToTH decs) (expToTH exp)
expToTH (DSigE exp ty)       = SigE (expToTH exp) (typeToTH ty)

matchToTH :: DMatch -> Match
matchToTH (DMatch pat exp) = Match (patToTH pat) (NormalB (expToTH exp)) []

patToTH :: DPat -> Pat
patToTH (DLitPa lit)    = LitP lit
patToTH (DVarPa n)      = VarP n
patToTH (DConPa n pats) = ConP n (map patToTH pats)
patToTH (DTildePa pat)  = TildeP (patToTH pat)
patToTH (DBangPa pat)   = BangP (patToTH pat)
patToTH DWildPa         = WildP

letDecToTH :: DLetDec -> Dec
letDecToTH (DFunD name clauses) = FunD name (map clauseToTH clauses)
letDecToTH (DValD pat exp)      = ValD (patToTH pat) (NormalB (expToTH exp)) []
letDecToTH (DSigD name ty)      = SigD name (typeToTH ty)
letDecToTH (DInfixD f name)     = InfixD f name

clauseToTH :: DClause -> Clause
clauseToTH (DClause pats exp) = Clause (map patToTH pats) (NormalB (expToTH exp)) []

typeToTH :: DType -> Type
typeToTH (DForallT tvbs cxt ty) = ForallT (map tvbToTH tvbs) (map predToTH cxt) (typeToTH ty)
typeToTH (DAppT t1 t2)          = AppT (typeToTH t1) (typeToTH t2)
typeToTH (DSigT ty ki)          = SigT (typeToTH ty) (kindToTH ki)
typeToTH (DVarT n)              = VarT n
typeToTH (DConT n)              = ConT n
typeToTH DArrowT                = ArrowT
typeToTH (DLitT lit)            = LitT lit

tvbToTH :: DTyVarBndr -> TyVarBndr
tvbToTH (DPlainTV n)           = PlainTV n
tvbToTH (DKindedTV n k)        = KindedTV n (kindToTH k)

predToTH :: DPred -> Pred
#if __GLASGOW_HASKELL__ < 709
predToTH = go []
  where
    go acc (DAppPr p t) = go (typeToTH t : acc) p
    go acc (DSigPr p _) = go acc                p  -- this shouldn't happen.
    go _   (DVarPr _)
      = error "Template Haskell in GHC <= 7.8 does not support variable constraints."
    go acc (DConPr n) 
      | nameBase n == "(~)"
      , [t1, t2] <- acc
      = EqualP t1 t2
      | otherwise
      = ClassP n acc
#else
predToTH (DAppPr p t) = AppT (predToTH p) (typeToTH t)
predToTH (DSigPr p k) = SigT (predToTH p) (kindToTH k)
predToTH (DVarPr n)   = VarT n
predToTH (DConPr n)   = ConT n
#endif

kindToTH :: DKind -> Kind
kindToTH (DForallK names ki) = ForallT (map PlainTV names) [] (kindToTH ki)
kindToTH (DVarK n)           = VarT n
kindToTH (DConK n kis)       = foldl AppT (ConT n) (map kindToTH kis)
kindToTH (DArrowK k1 k2)     = AppT (AppT ArrowT (kindToTH k1)) (kindToTH k2)
kindToTH DStarK              = StarT