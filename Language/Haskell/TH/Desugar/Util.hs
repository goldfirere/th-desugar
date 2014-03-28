{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Utility functions for th-desugar package.
-}

{-# LANGUAGE CPP, TupleSections #-}

module Language.Haskell.TH.Desugar.Util where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax ( Quasi(..) )

import qualified Data.Set as S
import Data.Foldable
import Control.Applicative

-- | Reify a declaration, warning the user about splices if the reify fails.
-- The warning says that reification can fail if you try to reify a type in
-- the same splice as it is declared.
reifyWithWarning :: Quasi q => Name -> q Info
reifyWithWarning name = qRecover
  (fail $ "Looking up " ++ (show name) ++ " in the list of available " ++
        "declarations failed.\nThis lookup fails if the declaration " ++
        "referenced was made in the same Template\nHaskell splice as the use " ++
        "of the declaration. If this is the case, put\nthe reference to " ++
        "the declaration in a new splice.")
  (qReify name)

-- | Report that a certain TH construct is impossible
impossible :: Quasi q => String -> q a
impossible err = fail (err ++ "\nThis should not happen in Haskell.\nPlease email eir@cis.upenn.edu with your code if you see this.")

-- | Extract the @TyVarBndr@s and constructors given the @Name@ of a type
getDataD :: Quasi q
         => String       -- ^ Print this out on failure
         -> Name         -- ^ Name of the datatype (@data@ or @newtype@) of interest
         -> q ([TyVarBndr], [Con])
getDataD err name = do
  info <- reifyWithWarning name
  dec <- case info of
           TyConI dec -> return dec
           _ -> badDeclaration
  case dec of
    DataD _cxt _name tvbs cons _derivings -> return (tvbs, cons)
    NewtypeD _cxt _name tvbs con _derivings -> return (tvbs, [con])
    _ -> badDeclaration
  where badDeclaration =
          fail $ "The name (" ++ (show name) ++ ") refers to something " ++
                 "other than a datatype. " ++ err

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: Quasi q => Name -> q Con
dataConNameToCon con_name = do
  -- we need to get the field ordering from the constructor. We must reify
  -- the constructor to get the tycon, and then reify the tycon to get the `Con`s
  info <- reifyWithWarning con_name
  type_name <- case info of
                 DataConI _name _type parent_name _fixity -> return parent_name
                 _ -> impossible "Non-data-con used to construct a record."
  (_, cons) <- getDataD "This seems to be an error in GHC." type_name
  let m_con = find ((con_name ==) . get_con_name) cons
  case m_con of
    Just con -> return con
    Nothing -> impossible "Datatype does not contain one of its own constructors."

  where
    get_con_name (NormalC name _)  = name
    get_con_name (RecC name _)     = name
    get_con_name (InfixC _ name _) = name
    get_con_name (ForallC _ _ con) = get_con_name con

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

-- | Concatenate the result of a @mapM@
concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ [] = pure []
concatMapM f (a : as) = (++) <$> f a <*> concatMapM f as

-- like GHC's
splitAtList :: [a] -> [b] -> ([b], [b])
splitAtList [] x = ([], x)
splitAtList (_ : t) (x : xs) =
  let (as, bs) = splitAtList t xs in
  (x : as, bs)
splitAtList (_ : _) [] = ([], [])

-- | If a type is a fully-applied tuple type, break it down into a list
-- of its constituents. Otherwise, return Nothing.
splitTuple_maybe :: Type -> Maybe [Type]
splitTuple_maybe = go []
  where
    go acc (AppT left right) = go (right:acc) left
    go acc (SigT ty _)       = go acc ty
    go acc (TupleT n)
      | n == length acc = Just acc
    go acc (ConT name)
      | Just n <- tupleNameDegree_maybe name
      , n == length acc = Just acc
    go _ _ = Nothing

-- | Extract the degree of a tuple, if the argument is a tuple
tupleDegree_maybe :: String -> Maybe Int
tupleDegree_maybe s = do
  '(' : s1 <- return s
  (commas, ")") <- return $ span (== ',') s1
  let degree
        | "" <- commas = 0
        | otherwise    = length commas + 1
  return degree

-- | Extract the degree of a tuple name, if the argument is a tuple name
tupleNameDegree_maybe :: Name -> Maybe Int
tupleNameDegree_maybe = tupleDegree_maybe . nameBase

liftSnd :: (a -> b) -> (c, a) -> (c, b)
liftSnd f (c, a) = (c, f a)

liftSndM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
liftSndM f (c, a) = f a >>= return . (c, )

liftThdOf3 :: (a -> b) -> (c, d, a) -> (c, d, b)
liftThdOf3 f (c, d, a) = (c, d, f a)

liftThdOf3M :: Monad m => (a -> m b) -> (c, d, a) -> m (c, d, b)
liftThdOf3M f (c, d, a) = f a >>= return . (c, d, )