{- Language/Haskell/TH/Desugar/FV.hs

(c) Ryan Scott 2018

Compute free variables of programs.
-}

{-# LANGUAGE CPP #-}
module Language.Haskell.TH.Desugar.FV
  ( fvDExp
  , fvDMatch
  , fvDClause
  , fvDType
  , fvDLetDecs

  , extractBoundNamesDLetDec
  , extractBoundNamesDPat
  ) where

#if __GLASGOW_HASKELL__ < 710
import Data.Foldable (foldMap)
#endif
#if __GLASGOW_HASKELL__ < 804
import Data.Monoid ((<>))
#endif
import qualified Data.Set as S
import Data.Set (Set)
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.AST

-- | Compute the free variables of a 'DExp'.
fvDExp :: DExp -> Set Name
fvDExp = go
  where
    go :: DExp -> Set Name
    go (DVarE n)         = S.singleton n
    go (DConE {})        = S.empty
    go (DLitE {})        = S.empty
    go (DAppE e1 e2)     = go e1 <> go e2
    go (DAppTypeE e t)   = go e <> fvDType t
    go (DLamE ns e)      = go e S.\\ S.fromList ns
    go (DCaseE scrut ms) = go scrut <> foldMap fvDMatch ms
    go (DLetE lds e)     = fvDLetDecs lds (go e)
    go (DSigE e t)       = go e <> fvDType t
    go (DStaticE e)      = go e

-- | Compute the free variables of a 'DMatch'.
fvDMatch :: DMatch -> Set Name
fvDMatch (DMatch pa e) = fv_dpat pa (fvDExp e)

-- | Compute the free variables of a 'DClause'.
fvDClause :: DClause -> Set Name
fvDClause (DClause pas e) = fv_dpats pas (fvDExp e)

-- | Compute the free variables of a 'DType'.
fvDType :: DType -> Set Name
fvDType = go
  where
    go :: DType -> Set Name
    go (DForallT tvbs ctxt ty) = fv_dtvbs tvbs (foldMap fvDType ctxt <> go ty)
    go (DAppT t1 t2)           = go t1 <> go t2
    go (DSigT ty ki)           = go ty <> go ki
    go (DVarT n)               = S.singleton n
    go (DConT {})              = S.empty
    go DArrowT                 = S.empty
    go (DLitT {})              = S.empty
    go DWildCardT              = S.empty

-- | Compute the free variables of a single 'DLetDec'.
--
-- If you are trying to compute the free variables of a list of 'DLetDec's, use
-- 'fv_dletdecs' instead, since it takes recursive @let@-bindings into account.
fv_dletdec :: DLetDec -> Set Name
fv_dletdec = go
  where
    go :: DLetDec -> Set Name
    go (DFunD n cs)    = S.delete n (foldMap fvDClause cs)
    go (DValD pa e)    = fv_dpat pa (fvDExp e)
    go (DSigD _ t)     = fvDType t -- A function's type can't mention its name
    go (DInfixD _ n)   = S.singleton n
    go (DPragmaD prag) = fv_dpragma prag

-- | Compute the free variables of a 'DPragma'.
fv_dpragma :: DPragma -> Set Name
fv_dpragma = go
  where
    go :: DPragma -> Set Name
    go (DInlineP {})               = S.empty
    go (DSpecialiseP _ ty _ _)     = fvDType ty
    go (DSpecialiseInstP ty)       = fvDType ty
    go (DRuleP _ rbndrs lhs rhs _) = fv_drule_bndrs rbndrs (fvDExp lhs <> fvDExp rhs)
    go (DAnnP _ e)                 = fvDExp e
    go (DLineP {})                 = S.empty
    go (DCompleteP cns tn)         = S.fromList cns <> foldMap S.singleton tn

-----
-- Extracting bound term names
-----

-- | Extract the term variables bound by a 'DLetDec'.
--
-- This does /not/ extract any type variables bound by pattern signatures
-- within 'DValD's.
-- (GHC won't accept something like @let Just (x :: [a]) = Just \"a\" in id \@a 'x'@
-- anyways.)
extractBoundNamesDLetDec :: DLetDec -> Set Name
extractBoundNamesDLetDec = go
  where
    go :: DLetDec -> Set Name
    go (DFunD n _)   = S.singleton n
    go (DValD pa _)  = extractBoundNamesDPat pa
    go (DSigD n _)   = S.singleton n
    go (DInfixD {})  = S.empty
    go (DPragmaD {}) = S.empty

-- | Extract the term variables bound by a 'DPat'.
--
-- This does /not/ extract any type variables bound by pattern signatures.
extractBoundNamesDPat :: DPat -> Set Name
extractBoundNamesDPat = go
  where
    go :: DPat -> Set Name
    go (DLitP _)      = S.empty
    go (DVarP n)      = S.singleton n
    go (DConP _ pats) = foldMap go pats
    go (DTildeP p)    = go p
    go (DBangP p)     = go p
    go (DSigP p _)    = go p
    go DWildP         = S.empty

-----
-- Binding forms
-----

-- | Adjust the free variables of something following 'DLetDec's.
fvDLetDecs :: [DLetDec] -> Set Name -> Set Name
fvDLetDecs lds fvs = (foldMap fv_dletdec lds <> fvs)
                        S.\\ foldMap extractBoundNamesDLetDec lds

-- | Adjust the free variables of something following 'DRuleBndr's.
fv_drule_bndrs :: [DRuleBndr] -> Set Name -> Set Name
fv_drule_bndrs rbndrs fvs = foldr fv_drule_bndr fvs rbndrs

-- | Adjust the free variables of something following a 'DRuleBndr'.
fv_drule_bndr :: DRuleBndr -> Set Name -> Set Name
fv_drule_bndr (DRuleVar n)        fvs = S.delete n fvs
fv_drule_bndr (DTypedRuleVar n t) fvs = S.delete n fvs <> fvDType t

-- | Adjust the free variables of something following 'DPat's.
fv_dpats :: [DPat] -> Set Name -> Set Name
fv_dpats pas fvs = foldr fv_dpat fvs pas

-- | Adjust the free variables of something following a 'DPat'.
fv_dpat :: DPat -> Set Name -> Set Name
fv_dpat dpa fvs = go dpa
  where
    go :: DPat -> Set Name
    go (DLitP {})    = fvs
    go (DVarP n)     = S.delete n fvs
    go (DConP _ pas) = fv_dpats pas fvs
    go (DTildeP pa)  = go pa
    go (DBangP  pa)  = go pa
    go (DSigP pa t)  = go pa S.\\ fvDType t
                          -- Unlike extractBoundNamesDPat, this /does/ extract
                          -- type variables bound by pattern signatures.
    go DWildP        = fvs

-- | Adjust the free variables of something following 'DTyVarBndr's.
fv_dtvbs :: [DTyVarBndr] -> Set Name -> Set Name
fv_dtvbs tvbs fvs = foldr fv_dtvb fvs tvbs

-- | Adjust the free variables of something following a 'DTyVarBndr'.
fv_dtvb :: DTyVarBndr -> Set Name -> Set Name
fv_dtvb (DPlainTV n)    fvs = S.delete n fvs
fv_dtvb (DKindedTV n k) fvs = S.delete n fvs <> fvDType k
