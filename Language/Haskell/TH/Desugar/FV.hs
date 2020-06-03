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
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.AST
import qualified Language.Haskell.TH.Desugar.OSet as OS
import Language.Haskell.TH.Desugar.OSet (OSet)

-- | Compute the free variables of a 'DType'.
fvDType :: DType -> OSet Name
fvDType = go
  where
    go :: DType -> OSet Name
    go (DForallT tele ty)      = fv_dtele tele (go ty)
    go (DConstrainedT ctxt ty) = foldMap fvDType ctxt <> go ty
    go (DAppT t1 t2)           = go t1 <> go t2
    go (DAppKindT t k)         = go t <> go k
    go (DSigT ty ki)           = go ty <> go ki
    go (DVarT n)               = OS.singleton n
    go (DConT {})              = OS.empty
    go DArrowT                 = OS.empty
    go (DLitT {})              = OS.empty
    go DWildCardT              = OS.empty

-----
-- Extracting bound term names
-----

-- | Extract the term variables bound by a 'DPat'.
--
-- This does /not/ extract any type variables bound by pattern signatures.
extractBoundNamesDPat :: DPat -> OSet Name
extractBoundNamesDPat = go
  where
    go :: DPat -> OSet Name
    go (DLitP _)      = OS.empty
    go (DVarP n)      = OS.singleton n
    go (DConP _ pats) = foldMap go pats
    go (DTildeP p)    = go p
    go (DBangP p)     = go p
    go (DSigP p _)    = go p
    go DWildP         = OS.empty

-----
-- Binding forms
-----

-- | Adjust the free variables of something following a 'DForallTelescope'.
fv_dtele :: DForallTelescope -> OSet Name -> OSet Name
fv_dtele (DForallVis   tvbs) = fv_dtvbs tvbs
fv_dtele (DForallInvis tvbs) = fv_dtvbs tvbs

-- | Adjust the free variables of something following 'DTyVarBndr's.
fv_dtvbs :: [DTyVarBndr flag] -> OSet Name -> OSet Name
fv_dtvbs tvbs fvs = foldr fv_dtvb fvs tvbs

-- | Adjust the free variables of something following a 'DTyVarBndr'.
fv_dtvb :: DTyVarBndr flag -> OSet Name -> OSet Name
fv_dtvb (DPlainTV n _)    fvs = OS.delete n fvs
fv_dtvb (DKindedTV n _ k) fvs = OS.delete n fvs <> fvDType k
