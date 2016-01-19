{- Language/Haskell/TH/Desugar/Expand.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE CPP, NoMonomorphismRestriction #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Expand
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (eir@cis.upenn.edu)
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
  expandUnsoundly,

  -- * Capture-avoiding substitution
  substTy
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Language.Haskell.TH hiding (cxt)
import Language.Haskell.TH.Syntax ( Quasi(..) )
import Data.Data
import Data.Generics
import Data.List
import qualified Data.Traversable as T

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.TH.Desugar.Reify

-- | Ignore kind annotations?
data IgnoreKinds = YesIgnore | NoIgnore

-- | Expands all type synonyms in a desugared type. Also expands open type family
-- applications, as long as the arguments have no free variables. Attempts to
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

#if __GLASGOW_HASKELL__ > 710
    DTyConI (DOpenTypeFamilyD _n tvbs _frs _ann) _
#else
    DTyConI (DFamilyD TypeFam _n tvbs _mkind) _
#endif
      |  length args >= length tvbs   -- this should always be true!
      ,  args_ok
      -> do
        let (syn_args, rest_args) = splitAtList tvbs args
        -- need to get the correct instance
        insts <- qReifyInstances n (map typeToTH syn_args)
        dinsts <- dsDecs insts
        case dinsts of
          [DTySynInstD _n (DTySynEqn lhs rhs)] -> do
            subst <-
              expectJustM "Impossible: reification returned a bogus instance" $
              merge_maps $ zipWith build_subst lhs syn_args
            ty <- substTy subst rhs
            ty' <- expand_type ign ty
            return $ foldl DAppT ty' rest_args
          _ -> return $ foldl DAppT (DConT n) args

#if __GLASGOW_HASKELL__ > 710
    DTyConI (DClosedTypeFamilyD _n tvbs _frs _ann eqns) _
#else
    DTyConI (DClosedTypeFamilyD _n tvbs _resk eqns) _
#endif
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
          let m_subst = merge_maps $ zipWith build_subst lhs arg_tys
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
#if __GLASGOW_HASKELL__ > 710
        Just (DTyConI (DOpenTypeFamilyD {}) _)   -> False
        Just (DTyConI (DDataFamilyD {}) _)       -> False
#else        
        Just (DTyConI (DFamilyD {}) _)           -> False
#endif
        Just (DTyConI (DClosedTypeFamilyD {}) _) -> False
        _                                        -> True
    no_tyvar_tyfam t = gmapQl (liftM2 (&&)) (return True) no_tyvars_tyfams t

    build_subst :: DType -> DType -> Maybe (M.Map Name DType)
    build_subst (DVarT var_name) arg = Just $ M.singleton var_name arg
      -- if a pattern has a kind signature, it's really easy to get
      -- this wrong.
    build_subst (DSigT ty _ki) arg = case ign of
      YesIgnore -> build_subst ty arg
      NoIgnore  -> Nothing
      -- but we can safely ignore kind signatures on the target
    build_subst pat (DSigT ty _ki) = build_subst pat ty
    build_subst (DForallT {}) _ =
      error "Impossible: forall-quantified pattern to type family"
      -- reifyInstances should fail if an argument is forall-quantified.
    build_subst _ (DForallT {}) =
      error "Impossible: forall-quantified argument to type family"
    build_subst (DAppT pat1 pat2) (DAppT arg1 arg2) =
      merge_maps [build_subst pat1 arg1, build_subst pat2 arg2]
    build_subst (DConT pat_con) (DConT arg_con)
      | pat_con == arg_con = Just M.empty
    build_subst DArrowT DArrowT = Just M.empty
    build_subst (DLitT pat_lit) (DLitT arg_lit)
      | pat_lit == arg_lit = Just M.empty
    build_subst _ _ = Nothing

    merge_maps :: [Maybe (M.Map Name DType)] -> Maybe (M.Map Name DType)
    merge_maps = foldl' merge_map1 (Just M.empty)

    merge_map1 :: Maybe (M.Map Name DType) -> Maybe (M.Map Name DType)
               -> Maybe (M.Map Name DType)
    merge_map1 ma mb = do
      a <- ma
      b <- mb
      let shared_key_set = M.keysSet a `S.intersection` M.keysSet b
          matches_up     = S.foldr (\name -> ((a M.! name) `geq` (b M.! name) &&))
                                   True shared_key_set
      if matches_up then return (a `M.union` b) else Nothing

    allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
    allM f = foldM (\b x -> (b &&) `liftM` f x) True

-- | Capture-avoiding substitution on types
substTy :: DsMonad q => M.Map Name DType -> DType -> q DType
substTy vars (DForallT tvbs cxt ty) =
  substTyVarBndrs vars tvbs $ \vars' tvbs' -> do
    cxt' <- mapM (substPred vars') cxt
    ty' <- substTy vars' ty
    return $ DForallT tvbs' cxt' ty'
substTy vars (DAppT t1 t2) =
  DAppT <$> substTy vars t1 <*> substTy vars t2
substTy vars (DSigT ty ki) =
  DSigT <$> substTy vars ty <*> pure ki
substTy vars (DVarT n)
  | Just ty <- M.lookup n vars
  = return ty
  | otherwise
  = return $ DVarT n
substTy _ ty = return ty

substTyVarBndrs :: DsMonad q => M.Map Name DType -> [DTyVarBndr]
                -> (M.Map Name DType -> [DTyVarBndr] -> q DType)
                -> q DType
substTyVarBndrs vars tvbs thing = do
  new_names <- mapM (const (qNewName "local")) tvbs
  let new_vars = M.fromList (zip (map extractDTvbName tvbs) (map DVarT new_names))
  -- this is very inefficient. Oh well.
  thing (M.union vars new_vars) (zipWith substTvb tvbs new_names)

substTvb :: DTyVarBndr -> Name -> DTyVarBndr
substTvb (DPlainTV _) n = DPlainTV n
substTvb (DKindedTV _ k) n = DKindedTV n k

-- | Extract the name from a @TyVarBndr@
extractDTvbName :: DTyVarBndr -> Name
extractDTvbName (DPlainTV n) = n
extractDTvbName (DKindedTV n _) = n

substPred :: DsMonad q => M.Map Name DType -> DPred -> q DPred
substPred vars (DAppPr p t) = DAppPr <$> substPred vars p <*> substTy vars t
substPred vars (DSigPr p k) = DSigPr <$> substPred vars p <*> pure k
substPred vars (DVarPr n)
  | Just ty <- M.lookup n vars
  = dTypeToDPred ty
  | otherwise
  = return $ DVarPr n
substPred _ p = return p

-- | Convert a 'DType' to a 'DPred'
dTypeToDPred :: DsMonad q => DType -> q DPred
dTypeToDPred (DForallT _ _ _) = impossible "Forall-type used as constraint"
dTypeToDPred (DAppT t1 t2)   = DAppPr <$> dTypeToDPred t1 <*> pure t2
dTypeToDPred (DSigT ty ki)   = DSigPr <$> dTypeToDPred ty <*> pure ki
dTypeToDPred (DVarT n)       = return $ DVarPr n
dTypeToDPred (DConT n)       = return $ DConPr n
dTypeToDPred DArrowT         = impossible "Arrow used as head of constraint"
dTypeToDPred (DLitT _)       = impossible "Type literal used as head of constraint"
dTypeToDPred DWildCardT      = return DWildCardPr

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
