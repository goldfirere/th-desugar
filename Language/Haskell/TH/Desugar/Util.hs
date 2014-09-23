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
  stripVarP_maybe, extractBoundNamesStmt, concatMapM,
  liftSndM, liftThdOf3M, stripPlainTV_maybe,
  liftSnd, liftThdOf3, splitAtList, extractBoundNamesDec,
  extractBoundNamesPat
  ) where

import Prelude hiding (mapM, foldl, concatMap, any)

import Language.Haskell.TH hiding ( cxt )
import Language.Haskell.TH.Syntax

import qualified Data.Set as S
import Data.Foldable
import Data.Generics hiding ( Fixity )
import Data.Traversable
import Data.Monoid

-- | Like newName, but even more unique (unique across different splices),
-- and with unique @nameBase@s.
newUniqueName :: Quasi q => String -> q Name
newUniqueName str = do
  n <- qNewName str
  qNewName $ show n

-- | Report that a certain TH construct is impossible
impossible :: Quasi q => String -> q a
impossible err = fail (err ++ "\n    This should not happen in Haskell.\n    Please email eir@cis.upenn.edu with your code if you see this.")

-- | Check if a name occurs anywhere within a TH tree.
nameOccursIn :: Data a => Name -> a -> Bool
nameOccursIn n = everything (||) $ mkQ False (== n)

-- | Extract all Names mentioned in a TH tree.
allNamesIn :: Data a => a -> [Name]
allNamesIn = everything (++) $ mkQ [] (:[])
               
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

-- like GHC's
splitAtList :: [a] -> [b] -> ([b], [b])
splitAtList [] x = ([], x)
splitAtList (_ : t) (x : xs) =
  let (as, bs) = splitAtList t xs in
  (x : as, bs)
splitAtList (_ : _) [] = ([], [])

liftSnd :: (a -> b) -> (c, a) -> (c, b)
liftSnd f (c, a) = (c, f a)

liftSndM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
liftSndM f (c, a) = f a >>= return . (c, )

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
