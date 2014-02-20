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
import Control.Monad
import Control.Applicative
import Language.Haskell.TH hiding (cxt)
import Language.Haskell.TH.Syntax ( Quasi(..) )
import Data.Data
import Data.Generics

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util

-- | Expands all type synonyms in a desugared type.
expandType :: Quasi q => DType -> q DType
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
    go args (DConT n) = expandCon n args
    go args ty = return $ foldl DAppT ty args

-- | Expands all type synonyms in a desugared predicate.
expandPred :: Quasi q => DPred -> q DPred
expandPred = go []
  where
    go args (DAppPr p t) = do
      t' <- expandType t
      go (t' : args) p
    go args (DSigPr p k) = do
      p' <- go [] p
      return $ foldl DAppPr (DSigPr p' k) args
    go args (DConPr n) = do
      ty <- expandCon n args
      dTypeToDPred ty
    go args p = return $ foldl DAppPr p args

-- | Expand a constructor with given arguments
expandCon :: Quasi q
          => Name     -- ^ Tycon name
          -> [DType]  -- ^ Arguments
          -> q DType  -- ^ Expanded type
expandCon n args = do
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

-- | Capture-avoiding substitution on types
substTy :: Quasi q => M.Map Name DType -> DType -> q DType
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

substTyVarBndrs :: Quasi q => M.Map Name DType -> [DTyVarBndr]
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

substPred :: Quasi q => M.Map Name DType -> DPred -> q DPred
substPred vars (DAppPr p t) = DAppPr <$> substPred vars p <*> substTy vars t
substPred vars (DSigPr p k) = DSigPr <$> substPred vars p <*> pure k
substPred vars (DVarPr n)
  | Just ty <- M.lookup n vars
  = dTypeToDPred ty
  | otherwise
  = return $ DVarPr n
substPred _ p = return p

-- | Convert a 'DType' to a 'DPred'
dTypeToDPred :: Quasi q => DType -> q DPred
dTypeToDPred (DForallT _ _ _) = impossible "Forall-type used as constraint"
dTypeToDPred (DAppT t1 t2)   = DAppPr <$> dTypeToDPred t1 <*> pure t2
dTypeToDPred (DSigT ty ki)   = DSigPr <$> dTypeToDPred ty <*> pure ki
dTypeToDPred (DVarT n)       = return $ DVarPr n
dTypeToDPred (DConT n)       = return $ DConPr n
dTypeToDPred DArrowT         = impossible "Arrow used as head of constraint"
dTypeToDPred (DLitT _)       = impossible "Type literal used as head of constraint"


-- | Expand all type synonyms in the desugared abstract syntax tree provided.
-- Normally, the first parameter should have a type like 'DExp' or 'DLetDec'.
expand :: (Quasi q, Data a) => a -> q a
expand = everywhereM (mkM expandType >=> mkM expandPred)