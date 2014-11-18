{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Utility functions for th-desugar package.
-}

{-# LANGUAGE CPP, TupleSections #-}

module Language.Haskell.TH.Desugar.Util (
  newUniqueName,
  impossible, 
  nameOccursIn, allNamesIn, mkTypeName, mkDataName,
  stripVarP_maybe, extractBoundNamesStmt,
  concatMapM, mapMaybeM, expectJustM,
  liftSndM, liftThdOf3M, stripPlainTV_maybe,
  liftSnd, liftThdOf3, splitAtList, extractBoundNamesDec,
  extractBoundNamesPat,
  tvbName, tvbToType, nameMatches, freeNamesOfTypes, thdOf3, firstMatch,
  tupleDegree_maybe, tupleNameDegree_maybe, unboxedTupleDegree_maybe,
  unboxedTupleNameDegree_maybe, splitTuple_maybe
  ) where

import Prelude hiding (mapM, foldl, concatMap, any)

import Language.Haskell.TH hiding ( cxt )
import Language.Haskell.TH.Syntax

import Control.Arrow  ( second )
import qualified Data.Set as S
import Data.Foldable
import Data.Generics hiding ( Fixity )
import Data.Traversable
import Data.Maybe
import Data.Monoid

----------------------------------------
-- TH manipulations
----------------------------------------

-- | Like newName, but even more unique (unique across different splices),
-- and with unique @nameBase@s.
newUniqueName :: Quasi q => String -> q Name
newUniqueName str = do
  n <- qNewName str
  qNewName $ show n

-- | Like TH's @lookupTypeName@, but if this name is not bound, then we assume
-- it is declared in the current module.
mkTypeName :: Quasi q => String -> q Name
mkTypeName str = do
  m_name <- qLookupName True str
  case m_name of
    Just name -> return name
    Nothing -> do
      Loc { loc_package = pkg, loc_module = modu } <- qLocation
      return $ mkNameG_tc pkg modu str

-- | Like TH's @lookupDataName@, but if this name is not bound, then we assume
-- it is declared in the current module.
mkDataName :: Quasi q => String -> q Name
mkDataName str = do
  m_name <- qLookupName False str
  case m_name of
    Just name -> return name
    Nothing -> do
      Loc { loc_package = pkg, loc_module = modu } <- qLocation
      return $ mkNameG_d pkg modu str

-- | Extracts the name out of a variable pattern, or returns @Nothing@
stripVarP_maybe :: Pat -> Maybe Name
stripVarP_maybe (VarP name) = Just name
stripVarP_maybe _           = Nothing

-- | Extracts the name out of a @PlainTV@, or returns @Nothing@
stripPlainTV_maybe :: TyVarBndr -> Maybe Name
stripPlainTV_maybe (PlainTV n) = Just n
stripPlainTV_maybe _           = Nothing

-- | Report that a certain TH construct is impossible
impossible :: Monad q => String -> q a
impossible err = fail (err ++ "\n    This should not happen in Haskell.\n    Please email eir@cis.upenn.edu with your code if you see this.")

-- | Extract a 'Name' from a 'TyVarBndr'
tvbName :: TyVarBndr -> Name
tvbName (PlainTV n)    = n
tvbName (KindedTV n _) = n

-- | Convert a 'TyVarBndr' into a 'Type'
tvbToType :: TyVarBndr -> Type
tvbToType = VarT . tvbName

-- | Do two names name the same thing?
nameMatches :: Name -> Name -> Bool
nameMatches n1@(Name occ1 flav1) n2@(Name occ2 flav2)
  | NameS <- flav1 = occ1 == occ2
  | NameS <- flav2 = occ1 == occ2
  | NameQ mod1 <- flav1
  , NameQ mod2 <- flav2
  = mod1 == mod2 && occ1 == occ2
  | NameQ mod1 <- flav1
  , NameG _ _ mod2 <- flav2
  = mod1 == mod2 && occ1 == occ2
  | NameG _ _ mod1 <- flav1
  , NameQ mod2 <- flav2
  = mod1 == mod2 && occ1 == occ2
  | otherwise
  = n1 == n2

-- | Extract the degree of a tuple
tupleDegree_maybe :: String -> Maybe Int
tupleDegree_maybe s = do
  '(' : s1 <- return s
  (commas, ")") <- return $ span (== ',') s1
  let degree
        | "" <- commas = 0
        | otherwise    = length commas + 1
  return degree

-- | Extract the degree of a tuple name
tupleNameDegree_maybe :: Name -> Maybe Int
tupleNameDegree_maybe = tupleDegree_maybe . nameBase

-- | Extract the degree of an unboxed tuple
unboxedTupleDegree_maybe :: String -> Maybe Int
unboxedTupleDegree_maybe s = do
  '(' : '#' : s1 <- return s
  (commas, "#)") <- return $ span (== ',') s1
  let degree
        | "" <- commas = 0
        | otherwise    = length commas + 1
  return degree

-- | Extract the degree of a tuple name
unboxedTupleNameDegree_maybe :: Name -> Maybe Int
unboxedTupleNameDegree_maybe = unboxedTupleDegree_maybe . nameBase

-- | If the argument is a tuple type, return the components
splitTuple_maybe :: Type -> Maybe [Type]
splitTuple_maybe t = go [] t
  where go args (t1 `AppT` t2) = go (t2:args) t1
        go args (t1 `SigT` _k) = go args t1
        go args (ConT con_name)
          | Just degree <- tupleNameDegree_maybe con_name
          , length args == degree
          = Just args
        go args (TupleT degree)
          | length args == degree
          = Just args
        go _ _ = Nothing

----------------------------------------
-- Free names, etc.
----------------------------------------

-- | Check if a name occurs anywhere within a TH tree.
nameOccursIn :: Data a => Name -> a -> Bool
nameOccursIn n = everything (||) $ mkQ False (== n)

-- | Extract all Names mentioned in a TH tree.
allNamesIn :: Data a => a -> [Name]
allNamesIn = everything (++) $ mkQ [] (:[])
               
-- | Extract the names bound in a @Stmt@
extractBoundNamesStmt :: Stmt -> S.Set Name
extractBoundNamesStmt (BindS pat _) = extractBoundNamesPat pat
extractBoundNamesStmt (LetS decs)   = foldMap extractBoundNamesDec decs
extractBoundNamesStmt (NoBindS _)   = S.empty
extractBoundNamesStmt (ParS stmtss) = foldMap (foldMap extractBoundNamesStmt) stmtss

-- | Extract the names bound in a @Dec@ that could appear in a @let@ expression.
extractBoundNamesDec :: Dec -> S.Set Name
extractBoundNamesDec (FunD name _)  = S.singleton name
extractBoundNamesDec (ValD pat _ _) = extractBoundNamesPat pat
extractBoundNamesDec _              = S.empty

-- | Extract the names bound in a @Pat@
extractBoundNamesPat :: Pat -> S.Set Name
extractBoundNamesPat (LitP _)            = S.empty
extractBoundNamesPat (VarP name)         = S.singleton name
extractBoundNamesPat (TupP pats)         = foldMap extractBoundNamesPat pats
extractBoundNamesPat (UnboxedTupP pats)  = foldMap extractBoundNamesPat pats
extractBoundNamesPat (ConP _ pats)       = foldMap extractBoundNamesPat pats
extractBoundNamesPat (InfixP p1 _ p2)    = extractBoundNamesPat p1 `S.union`
                                           extractBoundNamesPat p2
extractBoundNamesPat (UInfixP p1 _ p2)   = extractBoundNamesPat p1 `S.union`
                                           extractBoundNamesPat p2
extractBoundNamesPat (ParensP pat)       = extractBoundNamesPat pat
extractBoundNamesPat (TildeP pat)        = extractBoundNamesPat pat
extractBoundNamesPat (BangP pat)         = extractBoundNamesPat pat
extractBoundNamesPat (AsP name pat)      = S.singleton name `S.union` extractBoundNamesPat pat
extractBoundNamesPat WildP               = S.empty
extractBoundNamesPat (RecP _ field_pats) = let (_, pats) = unzip field_pats in
                                           foldMap extractBoundNamesPat pats
extractBoundNamesPat (ListP pats)        = foldMap extractBoundNamesPat pats
extractBoundNamesPat (SigP pat _)        = extractBoundNamesPat pat
extractBoundNamesPat (ViewP _ pat)       = extractBoundNamesPat pat

freeNamesOfTypes :: [Type] -> S.Set Name
freeNamesOfTypes = mconcat . map go
  where
    go (ForallT tvbs cxt ty) = (go ty <> mconcat (map go_pred cxt))
                               S.\\ S.fromList (map tvbName tvbs)
    go (AppT t1 t2)          = go t1 <> go t2
    go (SigT ty _)           = go ty
    go (VarT n)              = S.singleton n
    go _                     = S.empty

#if __GLASGOW_HASKELL__ >= 709
    go_pred = go
#else
    go_pred (ClassP _ tys) = freeNamesOfTypes tys
    go_pred (EqualP t1 t2) = go t1 <> go t2
#endif

----------------------------------------
-- General utility
----------------------------------------

-- like GHC's
splitAtList :: [a] -> [b] -> ([b], [b])
splitAtList [] x = ([], x)
splitAtList (_ : t) (x : xs) =
  let (as, bs) = splitAtList t xs in
  (x : as, bs)
splitAtList (_ : _) [] = ([], [])

liftSnd :: (a -> b) -> (c, a) -> (c, b)
liftSnd = second

liftSndM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
liftSndM f (c, a) = f a >>= return . (c, )

thdOf3 :: (a,b,c) -> c
thdOf3 (_,_,c) = c

liftThdOf3 :: (a -> b) -> (c, d, a) -> (c, d, b)
liftThdOf3 f (c, d, a) = (c, d, f a)

liftThdOf3M :: Monad m => (a -> m b) -> (c, d, a) -> m (c, d, b)
liftThdOf3M f (c, d, a) = f a >>= return . (c, d, )

-- lift concatMap into a monad
-- could this be more efficient?
-- | Concatenate the result of a @mapM@
concatMapM :: (Monad monad, Monoid monoid, Traversable t)
           => (a -> monad monoid) -> t a -> monad monoid
concatMapM fn list = do
  bss <- mapM fn list
  return $ fold bss

-- like GHC's
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = return []
mapMaybeM f (x:xs) = do
  y <- f x
  ys <- mapMaybeM f xs
  return $ case y of
    Nothing -> ys
    Just z  -> z : ys

expectJustM :: Monad m => String -> Maybe a -> m a
expectJustM _   (Just x) = return x
expectJustM err Nothing  = fail err

firstMatch :: (a -> Maybe b) -> [a] -> Maybe b
firstMatch f xs = listToMaybe $ mapMaybe f xs
    
