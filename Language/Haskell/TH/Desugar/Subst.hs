{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Subst
-- Copyright   :  (C) 2018 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Capture-avoiding substitutions on 'DType's
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar.Subst (
  DSubst,

  -- * Capture-avoiding substitution
  substTy, substTyVarBndrs, unionSubsts, unionMaybeSubsts,

  -- * Matching a type template against a type
  IgnoreKinds(..), matchTy
  ) where

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Language.Haskell.TH.Desugar.AST
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.Util

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif

-- | A substitution is just a map from names to types
type DSubst = M.Map Name DType

-- | Capture-avoiding substitution on types
substTy :: Quasi q => DSubst -> DType -> q DType
substTy vars (DForallT fvf tvbs ty) =
  substTyVarBndrs vars tvbs $ \vars' tvbs' -> do
    ty' <- substTy vars' ty
    return $ DForallT fvf tvbs' ty'
substTy vars (DConstrainedT cxt ty) =
  DConstrainedT <$> mapM (substTy vars) cxt <*> substTy vars ty
substTy vars (DAppT t1 t2) =
  DAppT <$> substTy vars t1 <*> substTy vars t2
substTy vars (DAppKindT t k) =
  DAppKindT <$> substTy vars t <*> substTy vars k
substTy vars (DSigT ty ki) =
  DSigT <$> substTy vars ty <*> substTy vars ki
substTy vars (DVarT n)
  | Just ty <- M.lookup n vars
  = return ty
  | otherwise
  = return $ DVarT n
substTy _ ty@(DConT _)  = return ty
substTy _ ty@DArrowT    = return ty
substTy _ ty@(DLitT _)  = return ty
substTy _ ty@DWildCardT = return ty

substTyVarBndrs :: Quasi q => DSubst -> [DTyVarBndr]
                -> (DSubst -> [DTyVarBndr] -> q a)
                -> q a
substTyVarBndrs vars tvbs thing = do
  (vars', tvbs') <- mapAccumLM substTvb vars tvbs
  thing vars' tvbs'

substTvb :: Quasi q => DSubst -> DTyVarBndr
         -> q (DSubst, DTyVarBndr)
substTvb vars (DPlainTV n) = do
  new_n <- qNewName (nameBase n)
  return (M.insert n (DVarT new_n) vars, DPlainTV new_n)
substTvb vars (DKindedTV n k) = do
  new_n <- qNewName (nameBase n)
  k' <- substTy vars k
  return (M.insert n (DVarT new_n) vars, DKindedTV new_n k')

-- | Computes the union of two substitutions. Fails if both subsitutions map
-- the same variable to different types.
unionSubsts :: DSubst -> DSubst -> Maybe DSubst
unionSubsts a b =
  let shared_key_set = M.keysSet a `S.intersection` M.keysSet b
      matches_up     = S.foldr (\name -> ((a M.! name) == (b M.! name) &&))
                               True shared_key_set
  in
  if matches_up then return (a `M.union` b) else Nothing

---------------------------
-- Matching

-- | Ignore kind annotations in @matchTy@?
data IgnoreKinds = YesIgnore | NoIgnore

-- | @matchTy ign tmpl targ@ matches a type template @tmpl@ against a type
-- target @targ@. This returns a Map from names of type variables in the
-- type template to types if the types indeed match up, or @Nothing@ otherwise.
-- In the @Just@ case, it is guaranteed that every type variable mentioned
-- in the template is mapped by the returned substitution.
--
-- The first argument @ign@ tells @matchTy@ whether to ignore kind signatures
-- in the template. A kind signature in the template might mean that a type
-- variable has a more restrictive kind than otherwise possible, and that
-- mapping that type variable to a type of a different kind could be disastrous.
-- So, if we don't ignore kind signatures, this function returns @Nothing@ if
-- the template has a signature anywhere. If we do ignore kind signatures, it's
-- possible the returned map will be ill-kinded. Use at your own risk.
matchTy :: IgnoreKinds -> DType -> DType -> Maybe DSubst
matchTy _   (DVarT var_name) arg = Just $ M.singleton var_name arg
  -- if a pattern has a kind signature, it's really easy to get
  -- this wrong.
matchTy ign (DSigT ty _ki) arg = case ign of
  YesIgnore -> matchTy ign ty arg
  NoIgnore  -> Nothing
  -- but we can safely ignore kind signatures on the target
matchTy ign pat (DSigT ty _ki) = matchTy ign pat ty
matchTy _   (DForallT {}) _ =
  error "Cannot match a forall in a pattern"
matchTy _   _ (DForallT {}) =
  error "Cannot match a forall in a target"
matchTy ign (DAppT pat1 pat2) (DAppT arg1 arg2) =
  unionMaybeSubsts [matchTy ign pat1 arg1, matchTy ign pat2 arg2]
matchTy _   (DConT pat_con) (DConT arg_con)
  | pat_con == arg_con = Just M.empty
matchTy _   DArrowT DArrowT = Just M.empty
matchTy _   (DLitT pat_lit) (DLitT arg_lit)
  | pat_lit == arg_lit = Just M.empty
matchTy _ _ _ = Nothing

unionMaybeSubsts :: [Maybe DSubst] -> Maybe DSubst
unionMaybeSubsts = foldl' union_subst1 (Just M.empty)
  where
    union_subst1 :: Maybe DSubst -> Maybe DSubst -> Maybe DSubst
    union_subst1 ma mb = do
      a <- ma
      b <- mb
      unionSubsts a b
