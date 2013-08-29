{- Language/Haskell/TH/Desugar/Sweeten.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Converts desugared TH back into real TH.
-}

{-# LANGUAGE CPP #-}

{-| The functions in this module convert desugared Template Haskell back into
    proper Template Haskell. -}

module Language.Haskell.TH.Desugar.Sweeten where

import Language.Haskell.TH

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
patToTH (DLitP lit)    = LitP lit
patToTH (DVarP n)      = VarP n
patToTH (DConP n pats) = ConP n (map patToTH pats)
patToTH (DTildeP pat)  = TildeP (patToTH pat)
patToTH (DBangP pat)   = BangP (patToTH pat)
patToTH DWildP         = WildP

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
#if __GLASGOW_HASKELL__ >= 707
tvbToTH (DRoledTV n r)         = RoledTV n r
tvbToTH (DKindedRoledTV n k r) = KindedRoledTV n (kindToTH k) r
#endif

predToTH :: DPred -> Pred
predToTH (DClassP n tys) = ClassP n (map typeToTH tys)
predToTH (DEqualP t1 t2) = EqualP (typeToTH t1) (typeToTH t2)

kindToTH :: DKind -> Kind
kindToTH (DForallK names ki) = ForallT (map PlainTV names) [] (kindToTH ki)
kindToTH (DVarK n)           = VarT n
kindToTH (DConK n kis)       = foldl AppT (ConT n) (map kindToTH kis)
kindToTH (DArrowK k1 k2)     = AppT (AppT ArrowT (kindToTH k1)) (kindToTH k2)
kindToTH DStarK              = StarT