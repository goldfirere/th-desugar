{- Language/Haskell/TH/Desugar/Expand.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE CPP, NoMonomorphismRestriction #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Expand
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Expands type synonyms and type families in desugared types.
-- See also the package th-expand-syns for doing this to
-- non-desugared types.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar.Expand (
  -- * Expand synonyms soundly
  expand, expandType,

  -- * Expand synonyms potentially unsoundly
  expandUnsoundly
  ) where

import qualified Data.Map as M
import Control.Monad
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Language.Haskell.TH hiding (cxt)
import Language.Haskell.TH.Syntax ( Quasi(..) )
import Data.Data
import Data.Generics
import qualified Data.Traversable as T

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.TH.Desugar.Reify
import Language.Haskell.TH.Desugar.Subst

-- | Expands all type synonyms in a desugared type. Also expands open type family
-- applications. (In GHCs before 7.10, this part does not work if there are any
-- variables.) Attempts to
-- expand closed type family applications, but aborts the moment it spots anything
-- strange, like a nested type family application or type variable.
expandType :: DsMonad q => DType -> q DType
expandType = expand_type NoIgnore

expand_type :: DsMonad q => IgnoreKinds -> DType -> q DType
expand_type ign = go []
  where
    go [] (DForallT tvbs cxt ty) =
      DForallT tvbs <$> mapM (expand_ ign) cxt <*> expand_type ign ty
    go _ (DForallT {}) =
      impossible "A forall type is applied to another type."
    go args (DAppT t1 t2) = do
      t2' <- expand_type ign t2
      go (t2' : args) t1
    go args (DSigT ty ki) = do
      ty' <- go [] ty
      return $ foldl DAppT (DSigT ty' ki) args
    go args (DConT n) = expand_con ign n args
    go args ty = return $ foldl DAppT ty args

-- | Expands all type synonyms in a desugared predicate.
expand_pred :: DsMonad q => IgnoreKinds -> DPred -> q DPred
expand_pred ign = go []
  where
    go args (DAppPr p t) = do
      t' <- expand_type ign t
      go (t' : args) p
    go args (DSigPr p k) = do
      p' <- go [] p
      return $ foldl DAppPr (DSigPr p' k) args
    go args (DConPr n) = do
      ty <- expand_con ign n args
      dTypeToDPred ty
    go args p = return $ foldl DAppPr p args

-- | Expand a constructor with given arguments
expand_con :: DsMonad q
           => IgnoreKinds
           -> Name     -- ^ Tycon name
           -> [DType]  -- ^ Arguments
           -> q DType  -- ^ Expanded type
expand_con ign n args = do
  info <- reifyWithLocals n
  dinfo <- dsInfo info
  args_ok <- allM no_tyvars_tyfams args
  case dinfo of
    DTyConI (DTySynD _n tvbs rhs) _
      |  length args >= length tvbs   -- this should always be true!
      -> do
        let (syn_args, rest_args) = splitAtList tvbs args
        ty <- substTy (M.fromList $ zip (map extractDTvbName tvbs) syn_args) rhs
        ty' <- expand_type ign ty
        return $ foldl DAppT ty' rest_args

    DTyConI (DOpenTypeFamilyD (DTypeFamilyHead _n tvbs _frs _ann)) _
      |  length args >= length tvbs   -- this should always be true!
#if __GLASGOW_HASKELL__ < 709
      ,  args_ok
#endif
      -> do
        let (syn_args, rest_args) = splitAtList tvbs args
        -- We need to get the correct instance. If we fail to reify anything
        -- (e.g., if a type family is quasiquoted), then fall back by
        -- pretending that there are no instances in scope.
        insts <- qRecover (return []) $
                 qReifyInstances n (map typeToTH syn_args)
        dinsts <- dsDecs insts
        case dinsts of
          [DTySynInstD _n (DTySynEqn lhs rhs)] -> do
            subst <-
              expectJustM "Impossible: reification returned a bogus instance" $
              unionMaybeSubsts $ zipWith (matchTy ign) lhs syn_args
            ty <- substTy subst rhs
            ty' <- expand_type ign ty
            return $ foldl DAppT ty' rest_args
          _ -> return $ foldl DAppT (DConT n) args


    DTyConI (DClosedTypeFamilyD (DTypeFamilyHead _n tvbs _frs _ann) eqns) _
      |  length args >= length tvbs
      ,  args_ok
      -> do
        let (syn_args, rest_args) = splitAtList tvbs args
        rhss <- mapMaybeM (check_eqn syn_args) eqns
        case rhss of
          (rhs : _) -> do
            rhs' <- expand_type ign rhs
            return $ foldl DAppT rhs' rest_args
          [] -> return $ foldl DAppT (DConT n) args

      where
         -- returns the substed rhs
        check_eqn :: DsMonad q => [DType] -> DTySynEqn -> q (Maybe DType)
        check_eqn arg_tys (DTySynEqn lhs rhs) = do
          let m_subst = unionMaybeSubsts $ zipWith (matchTy ign) lhs arg_tys
          T.mapM (flip substTy rhs) m_subst

    _ -> return $ foldl DAppT (DConT n) args

  where
    no_tyvars_tyfams :: (DsMonad q, Data a) => a -> q Bool
    no_tyvars_tyfams = everything (liftM2 (&&)) (mkQ (return True) no_tyvar_tyfam)

    no_tyvar_tyfam :: DsMonad q => DType -> q Bool
    no_tyvar_tyfam (DVarT _) = return False
    no_tyvar_tyfam (DConT con_name) = do
      m_info <- dsReify con_name
      return $ case m_info of
        Nothing -> False   -- we don't know anything. False is safe.
        Just (DTyConI (DOpenTypeFamilyD {}) _)   -> False
        Just (DTyConI (DDataFamilyD {}) _)       -> False
        Just (DTyConI (DClosedTypeFamilyD {}) _) -> False
        _                                        -> True
    no_tyvar_tyfam t = gmapQl (liftM2 (&&)) (return True) no_tyvars_tyfams t

    allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
    allM f = foldM (\b x -> (b &&) `liftM` f x) True

-- | Extract the name from a @TyVarBndr@
extractDTvbName :: DTyVarBndr -> Name
extractDTvbName (DPlainTV n) = n
extractDTvbName (DKindedTV n _) = n

-- | Expand all type synonyms and type families in the desugared abstract
-- syntax tree provided, where type family simplification is on a "best effort"
-- basis. Normally, the first parameter should have a type like
-- 'DExp' or 'DLetDec'.
expand :: (DsMonad q, Data a) => a -> q a
expand = expand_ NoIgnore

-- | Expand all type synonyms and type families in the desugared abstract
-- syntax tree provided, where type family simplification is on a "better
-- than best effort" basis. This means that it will try so hard that it will
-- sometimes do the wrong thing. Specifically, any kind parameters to type
-- families are ignored. So, if we have
--
-- > type family F (x :: k) where
-- >   F (a :: *) = Int
--
-- 'expandUnsoundly' will expand @F 'True@ to @Int@, ignoring that the
-- expansion should only work for type of kind @*@.
--
-- This function is useful because plain old 'expand' will simply fail
-- to expand type families that make use of kinds. Sometimes, the kinds
-- are benign and we want to expand anyway. Use this function in that case.
expandUnsoundly :: (DsMonad q, Data a) => a -> q a
expandUnsoundly = expand_ YesIgnore

-- | Generalization of 'expand' that either can or won't ignore kind annotations.sx
expand_ :: (DsMonad q, Data a) => IgnoreKinds -> a -> q a
expand_ ign = everywhereM (mkM (expand_type ign) >=> mkM (expand_pred ign))
