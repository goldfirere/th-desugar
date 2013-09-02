{- Language/Haskell/TH/Desugar/Expand.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE CPP #-}

{-| Expands type synonyms in desugared types, ignoring type families.
See also the package th-expand-syns for doing this to non-desugared types.
-}

module Language.Haskell.TH.Desugar.Expand (
  expand, expandType, substTy
  ) where

import qualified Data.Map as M
import Control.Applicative
import Language.Haskell.TH
import Data.Data
import Data.Generics

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util

-- | Expands all type synonyms in a desugared type.
expandType :: DType -> Q DType
expandType = go []
  where
    go [] (DForallT tvbs cxt ty) =
      DForallT tvbs <$> mapM expand cxt <*> expandType ty
    go _ (DForallT {}) =
      impossible "A forall type is applied to another type."
    go args (DAppT t1 t2) = do
      t2' <- expandType t2
      go (t2' : args) t1
    go args (DSigT ty ki) = do
      ty' <- go [] ty
      return $ foldl DAppT (DSigT ty' ki) args
    go args (DConT n) = do
      info <- reifyWithWarning n
      case info of
        TyConI (TySynD _n tvbs rhs)
          | length args >= length tvbs -> do
          let (syn_args, rest_args) = splitAtList tvbs args
          rhs' <- dsType rhs
          rhs'' <- expandType rhs'
          tvbs' <- mapM dsTvb tvbs
          ty <- substTy (M.fromList $ zip (map extractDTvbName tvbs') syn_args) rhs''
          return $ foldl DAppT ty rest_args
        _ -> return $ foldl DAppT (DConT n) args
    go args ty = return $ foldl DAppT ty args

-- | Capture-avoiding substitution on types
substTy :: M.Map Name DType -> DType -> Q DType
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

substTyVarBndrs :: M.Map Name DType -> [DTyVarBndr]
                -> (M.Map Name DType -> [DTyVarBndr] -> Q DType)
                -> Q DType
substTyVarBndrs vars tvbs thing = do
  new_names <- mapM (const (newName "local")) tvbs
  let new_vars = M.fromList (zip (map extractDTvbName tvbs) (map DVarT new_names))
  -- this is very inefficient. Oh well.
  thing (M.union vars new_vars) (zipWith substTvb tvbs new_names)

substTvb :: DTyVarBndr -> Name -> DTyVarBndr
substTvb (DPlainTV _) n = DPlainTV n
substTvb (DKindedTV _ k) n = DKindedTV n k
#if __GLASGOW_HASKELL__ >= 707
substTvb (DRoledTV _ r) n = DRoledTV n r
substTvb (DKindedRoledTV _ k r) n = DKindedRoledTV n k r
#endif

-- | Extract the name from a @TyVarBndr@
extractDTvbName :: DTyVarBndr -> Name
extractDTvbName (DPlainTV n) = n
extractDTvbName (DKindedTV n _) = n
#if __GLASGOW_HASKELL__ >= 707
extractDTvbName (DRoledTV n _) = n
extractDTvbName (DKindedRoledTV n _ _) = n
#endif

substPred :: M.Map Name DType -> DPred -> Q DPred
substPred vars (DClassP name tys) =
  DClassP name <$> mapM (substTy vars) tys
substPred vars (DEqualP t1 t2) =
  DEqualP <$> substTy vars t1 <*> substTy vars t2

-- | Expand all type synonyms in the desugared abstract syntax tree provided.
-- Normally, the first parameter should have a type like 'DExp' or 'DLetDec'.
expand :: Data a => a -> Q a
expand = everywhereM (mkM expandType)