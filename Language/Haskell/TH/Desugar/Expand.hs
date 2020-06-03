{- Language/Haskell/TH/Desugar/Expand.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE CPP, NoMonomorphismRestriction, ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Expand
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
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

import Language.Haskell.TH.Desugar.AST
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

expand_type :: forall q. DsMonad q => IgnoreKinds -> DType -> q DType
expand_type ign = go []
  where
    go :: [DTypeArg] -> DType -> q DType
    go [] (DForallT tele ty) =
      DForallT <$> expand_tele ign tele
               <*> expand_type ign ty
    go _ (DForallT {}) =
      impossible "A forall type is applied to another type."
    go [] (DConstrainedT cxt ty) =
      DConstrainedT <$> mapM (expand_type ign) cxt
                    <*> expand_type ign ty
    go _ (DConstrainedT {}) =
      impossible "A constrained type is applied to another type."
    go args (DAppT t1 t2) = do
      t2' <- expand_type ign t2
      go (DTANormal t2' : args) t1
    go args (DAppKindT p k) = do
      k' <- expand_type ign k
      go (DTyArg k' : args) p
    go args (DSigT ty ki) = do
      ty' <- go [] ty
      ki' <- go [] ki
      finish (DSigT ty' ki') args
    go args (DConT n) = expand_con ign n args
    go args ty@(DVarT _)  = finish ty args
    go args ty@DArrowT    = finish ty args
    go args ty@(DLitT _)  = finish ty args
    go args ty@DWildCardT = finish ty args

    finish :: DType -> [DTypeArg] -> q DType
    finish ty args = return $ applyDType ty args

-- | Expands all type synonyms in the kinds of a @forall@ telescope.
expand_tele :: DsMonad q => IgnoreKinds -> DForallTelescope -> q DForallTelescope
expand_tele ign (DForallVis   tvbs) = DForallVis   <$> mapM (expand_tvb ign) tvbs
expand_tele ign (DForallInvis tvbs) = DForallInvis <$> mapM (expand_tvb ign) tvbs

-- | Expands all type synonyms in a type variable binder's kind.
expand_tvb :: DsMonad q => IgnoreKinds -> DTyVarBndr flag -> q (DTyVarBndr flag)
expand_tvb _   tvb@DPlainTV{}       = pure tvb
expand_tvb ign (DKindedTV n flag k) = DKindedTV n flag <$> expand_type ign k

-- | Expand a constructor with given arguments
expand_con :: forall q.
              DsMonad q
           => IgnoreKinds
           -> Name       -- ^ Tycon name
           -> [DTypeArg] -- ^ Arguments
           -> q DType    -- ^ Expanded type
expand_con ign n args = do
  info <- reifyWithLocals n
  case info of
    TyConI (TySynD _ _ StarT)
         -- See Note [Don't expand synonyms for *]
      -> return $ applyDType (DConT typeKindName) args
    _ -> go info
  where
    -- Only the normal (i.e., non-visibly applied) arguments. These are
    -- important since we need to align these with the arguments of the type
    -- synonym/family, and visible kind arguments can mess with this.
    normal_args :: [DType]
    normal_args = filterDTANormals args

    go :: Info -> q DType
    go info = do
      dinfo <- dsInfo info
      args_ok <- allM no_tyvars_tyfams normal_args
      case dinfo of
        DTyConI (DTySynD _n tvbs rhs) _
          |  length normal_args >= length tvbs   -- this should always be true!
          -> do
            let (syn_args, rest_args) = splitAtList tvbs normal_args
            ty <- substTy (M.fromList $ zip (map dtvbName tvbs) syn_args) rhs
            ty' <- expand_type ign ty
            return $ applyDType ty' $ map DTANormal rest_args

        DTyConI (DOpenTypeFamilyD (DTypeFamilyHead _n tvbs _frs _ann)) _
          |  length normal_args >= length tvbs   -- this should always be true!
#if __GLASGOW_HASKELL__ < 709
          ,  args_ok
#endif
          -> do
            let (syn_args, rest_args) = splitAtList tvbs normal_args
            -- We need to get the correct instance. If we fail to reify anything
            -- (e.g., if a type family is quasiquoted), then fall back by
            -- pretending that there are no instances in scope.
            insts <- qRecover (return []) $
                     qReifyInstances n (map typeToTH syn_args)
            dinsts <- dsDecs insts
            case dinsts of
              [DTySynInstD (DTySynEqn _ lhs rhs)]
                |  (_, lhs_args) <- unfoldDType lhs
                ,  let lhs_normal_args = filterDTANormals lhs_args
                ,  Just subst <-
                     unionMaybeSubsts $ zipWith (matchTy ign) lhs_normal_args syn_args
                -> do ty <- substTy subst rhs
                      ty' <- expand_type ign ty
                      return $ applyDType ty' $ map DTANormal rest_args
              _ -> give_up


        DTyConI (DClosedTypeFamilyD (DTypeFamilyHead _n tvbs _frs _ann) eqns) _
          |  length normal_args >= length tvbs
          ,  args_ok
          -> do
            let (syn_args, rest_args) = splitAtList tvbs normal_args
            rhss <- mapMaybeM (check_eqn syn_args) eqns
            case rhss of
              (rhs : _) -> do
                rhs' <- expand_type ign rhs
                return $ applyDType rhs' $ map DTANormal rest_args
              [] -> give_up

          where
             -- returns the substed rhs
            check_eqn :: [DType] -> DTySynEqn -> q (Maybe DType)
            check_eqn arg_tys (DTySynEqn _ lhs rhs) = do
              let (_, lhs_args) = unfoldDType lhs
                  normal_lhs_args = filterDTANormals lhs_args
                  m_subst = unionMaybeSubsts $ zipWith (matchTy ign) normal_lhs_args arg_tys
              T.mapM (flip substTy rhs) m_subst

        _ -> give_up

    -- Used when we can't proceed with type family instance expansion any more,
    -- and must conservatively return the orignal type family applied to its
    -- arguments.
    give_up :: q DType
    give_up = return $ applyDType (DConT n) args

    no_tyvars_tyfams :: DType -> q Bool
    no_tyvars_tyfams = go_ty
      where
        go_ty :: DType -> q Bool
        -- Interesting cases
        go_ty (DVarT _) = return False
        go_ty (DConT con_name) = do
          m_info <- dsReify con_name
          return $ case m_info of
            Nothing -> False   -- we don't know anything. False is safe.
            Just (DTyConI (DOpenTypeFamilyD {}) _)   -> False
            Just (DTyConI (DDataFamilyD {}) _)       -> False
            Just (DTyConI (DClosedTypeFamilyD {}) _) -> False
            _                                        -> True

        -- Recursive cases
        go_ty (DForallT tele ty)      = liftM2 (&&) (go_tele tele) (go_ty ty)
        go_ty (DConstrainedT ctxt ty) = liftM2 (&&) (allM go_ty ctxt) (go_ty ty)
        go_ty (DAppT t1 t2)           = liftM2 (&&) (go_ty t1) (go_ty t2)
        go_ty (DAppKindT t k)         = liftM2 (&&) (go_ty t)  (go_ty k)
        go_ty (DSigT t k)             = liftM2 (&&) (go_ty t)  (go_ty k)

        -- Default to True
        go_ty DLitT{}    = return True
        go_ty DArrowT    = return True
        go_ty DWildCardT = return True

        -- These cases are uninteresting
        go_tele :: DForallTelescope -> q Bool
        go_tele (DForallVis   tvbs) = allM go_tvb tvbs
        go_tele (DForallInvis tvbs) = allM go_tvb tvbs

        go_tvb :: DTyVarBndr flag -> q Bool
        go_tvb DPlainTV{}        = return True
        go_tvb (DKindedTV _ _ k) = go_ty k

    allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
    allM f = foldM (\b x -> (b &&) `liftM` f x) True

{-
Note [Don't expand synonyms for *]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We deliberately avoid expanding type synonyms for * such as Type and ★.
Why? If you reify any such type synonym using Template Haskell, this is
what you'll get:

  TyConI (TySynD <type synonym name> [] StarT)

If you blindly charge ahead and recursively inspect the right-hand side of
this type synonym, you'll desugar StarT into (DConT ''Type), reify ''Type,
and get back another type synonym with StarT as its right-hand side. Then
you'll recursively inspect StarT and find yourself knee-deep in an infinite
loop.

To prevent these sorts of shenanigans, we simply stop whenever we see a type
synonym with StarT as its right-hand side and return Type.
-}

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
expand_ ign = everywhereM (mkM (expand_type ign))
