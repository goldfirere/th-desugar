{- Language/Haskell/TH/Desugar/FV.hs

(c) Ryan Scott 2018

Compute free variables of programs.
-}

{-# LANGUAGE CPP #-}
module Language.Haskell.TH.Desugar.FV
  ( fvDType
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

-- | Compute the free variables of a 'DType'.
fvDType :: DType -> Set Name
fvDType = go
  where
    go :: DType -> Set Name
    go (DForallT tvbs ctxt ty) = fv_dtvbs tvbs (foldMap fvDType ctxt <> go ty)
    go (DAppT t1 t2)           = go t1 <> go t2
    go (DAppKindT t k)         = go t <> go k
    go (DSigT ty ki)           = go ty <> go ki
    go (DVarT n)               = S.singleton n
    go (DConT {})              = S.empty
    go DArrowT                 = S.empty
    go (DLitT {})              = S.empty
    go DWildCardT              = S.empty

-----
-- Extracting bound term names
-----

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

-- | Adjust the free variables of something following 'DTyVarBndr's.
fv_dtvbs :: [DTyVarBndr] -> Set Name -> Set Name
fv_dtvbs tvbs fvs = foldr fv_dtvb fvs tvbs

-- | Adjust the free variables of something following a 'DTyVarBndr'.
fv_dtvb :: DTyVarBndr -> Set Name -> Set Name
fv_dtvb (DPlainTV n)    fvs = S.delete n fvs
fv_dtvb (DKindedTV n k) fvs = S.delete n fvs <> fvDType k
