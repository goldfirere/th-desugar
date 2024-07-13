-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Subst.Capturing
-- Copyright   :  (C) 2024 Ryan Scott
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Substitutions on 'DType's that do /not/ avoid capture. (For capture-avoiding
-- substitution functions, use "Language.Haskell.TH.Desugar.Subst" instead.)
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar.Subst.Capturing (
  DSubst,

  -- * Non–capture-avoiding substitution
  substTy, substForallTelescope, substTyVarBndrs, substTyVarBndr,
  unionSubsts, unionMaybeSubsts,

  -- * Matching a type template against a type
  IgnoreKinds(..), matchTy
  ) where

import Data.Bifunctor (second)
import qualified Data.List as L
import qualified Data.Map as M

import Language.Haskell.TH.Desugar.AST
import Language.Haskell.TH.Desugar.Subst
  (DSubst, unionSubsts, unionMaybeSubsts, IgnoreKinds(..), matchTy)

-- | Non–capture-avoiding substitution on 'DType's. Unlike the @substTy@
-- function in "Language.Haskell.TH.Desugar.Subst", this 'substTy' function is
-- pure, as it never needs to create fresh names.
substTy :: DSubst -> DType -> DType
substTy subst ty | M.null subst = ty
substTy subst (DForallT tele inner_ty)
  = DForallT tele' inner_ty'
  where
    (subst', tele') = substForallTelescope subst tele
    inner_ty'       = substTy subst' inner_ty
substTy subst (DConstrainedT cxt inner_ty) =
  DConstrainedT (map (substTy subst) cxt) (substTy subst inner_ty)
substTy subst (DAppT ty1 ty2) = substTy subst ty1 `DAppT` substTy subst ty2
substTy subst (DAppKindT ty ki) = substTy subst ty `DAppKindT` substTy subst ki
substTy subst (DSigT ty ki) = substTy subst ty `DSigT` substTy subst ki
substTy subst (DVarT n) =
  case M.lookup n subst of
    Just ki -> ki
    Nothing -> DVarT n
substTy _ ty@(DConT {}) = ty
substTy _ ty@(DArrowT)  = ty
substTy _ ty@(DLitT {}) = ty
substTy _ ty@DWildCardT = ty

-- | Non–capture-avoiding substitution on 'DForallTelescope's. This returns a
-- pair containing the new 'DSubst' as well as a new 'DForallTelescope' value,
-- where the kinds have been substituted.
substForallTelescope :: DSubst -> DForallTelescope -> (DSubst, DForallTelescope)
substForallTelescope s (DForallInvis tvbs) = second DForallInvis $ substTyVarBndrs s tvbs
substForallTelescope s (DForallVis   tvbs) = second DForallVis   $ substTyVarBndrs s tvbs

-- | Non–capture-avoiding substitution on a telescope of 'DTyVarBndr's. This
-- returns a pair containing the new 'DSubst' as well as a new telescope of
-- 'DTyVarBndr's, where the kinds have been substituted.
substTyVarBndrs :: DSubst -> [DTyVarBndr flag] -> (DSubst, [DTyVarBndr flag])
substTyVarBndrs = L.mapAccumL substTyVarBndr

-- | Non–capture-avoiding substitution on a 'DTyVarBndr'. This updates the
-- 'DSubst' to remove the 'DTyVarBndr' name from the domain (as that name is now
-- bound by the 'DTyVarBndr') and applies the substitution to the kind of the
-- 'DTyVarBndr'.
substTyVarBndr :: DSubst -> DTyVarBndr flag -> (DSubst, DTyVarBndr flag)
substTyVarBndr s tvb@(DPlainTV n _) = (M.delete n s, tvb)
substTyVarBndr s (DKindedTV n f k)  = (M.delete n s, DKindedTV n f (substTy s k))
