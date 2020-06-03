{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Utility functions for th-desugar package.
-}

{-# LANGUAGE CPP, DeriveDataTypeable, RankNTypes, ScopedTypeVariables, TupleSections #-}

#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications #-}
#endif

module Language.Haskell.TH.Desugar.Util (
  newUniqueName,
  impossible,
  nameOccursIn, allNamesIn, mkTypeName, mkDataName, mkNameWith, isDataName,
  stripVarP_maybe, extractBoundNamesStmt,
  concatMapM, mapAccumLM, mapMaybeM, expectJustM,
  stripPlainTV_maybe,
  thirdOf3, splitAtList, extractBoundNamesDec,
  extractBoundNamesPat,
  tvbToType, tvbToTypeWithSig, tvbToTANormalWithSig,
  nameMatches, thdOf3, liftFst, liftSnd, firstMatch,
  unboxedSumDegree_maybe, unboxedSumNameDegree_maybe,
  tupleDegree_maybe, tupleNameDegree_maybe, unboxedTupleDegree_maybe,
  unboxedTupleNameDegree_maybe, splitTuple_maybe,
  topEverywhereM, isInfixDataCon,
  isTypeKindName, typeKindName,
  unSigType, unfoldType, ForallTelescope(..), FunArgs(..), VisFunArg(..),
  filterVisFunArgs, ravelType, unravelType,
  TypeArg(..), applyType, filterTANormals, probablyWrongUnTypeArg
#if __GLASGOW_HASKELL__ >= 800
  , bindIP
#endif
  ) where

import Prelude hiding (mapM, foldl, concatMap, any)

import Language.Haskell.TH hiding ( cxt )
import Language.Haskell.TH.Datatype.TyVarBndr
import qualified Language.Haskell.TH.Desugar.OSet as OS
import Language.Haskell.TH.Desugar.OSet (OSet)
import Language.Haskell.TH.Syntax

import qualified Control.Monad.Fail as Fail
import Data.Foldable
import Data.Generics hiding ( Fixity )
import Data.Traversable
import Data.Maybe

#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

#if __GLASGOW_HASKELL__ >= 800
import qualified Data.Kind as Kind
import GHC.Classes ( IP )
import Unsafe.Coerce ( unsafeCoerce )
#endif

----------------------------------------
-- TH manipulations
----------------------------------------

-- | Like newName, but even more unique (unique across different splices),
-- and with unique @nameBase@s. Precondition: the string is a valid Haskell
-- alphanumeric identifier (could be upper- or lower-case).
newUniqueName :: Quasi q => String -> q Name
newUniqueName str = do
  n <- qNewName str
  qNewName $ show n

-- | @mkNameWith lookup_fun mkName_fun str@ looks up the exact 'Name' of @str@
-- using the function @lookup_fun@. If it finds 'Just' the 'Name', meaning
-- that it is bound in the current scope, then it is returned. If it finds
-- 'Nothing', it assumes that @str@ is declared in the current module, and
-- uses @mkName_fun@ to construct the appropriate 'Name' to return.
mkNameWith :: Quasi q => (String -> q (Maybe Name))
                      -> (String -> String -> String -> Name)
                      -> String -> q Name
mkNameWith lookup_fun mkName_fun str = do
  m_name <- lookup_fun str
  case m_name of
    Just name -> return name
    Nothing -> do
      Loc { loc_package = pkg, loc_module = modu } <- qLocation
      return $ mkName_fun pkg modu str

-- | Like TH's @lookupTypeName@, but if this name is not bound, then we assume
-- it is declared in the current module.
mkTypeName :: Quasi q => String -> q Name
mkTypeName = mkNameWith (qLookupName True) mkNameG_tc

-- | Like TH's @lookupDataName@, but if this name is not bound, then we assume
-- it is declared in the current module.
mkDataName :: Quasi q => String -> q Name
mkDataName = mkNameWith (qLookupName False) mkNameG_d

-- | Is this name a data constructor name? A 'False' answer means "unsure".
isDataName :: Name -> Bool
isDataName (Name _ (NameG DataName _ _)) = True
isDataName _                             = False

-- | Extracts the name out of a variable pattern, or returns @Nothing@
stripVarP_maybe :: Pat -> Maybe Name
stripVarP_maybe (VarP name) = Just name
stripVarP_maybe _           = Nothing

-- | Extracts the name out of a @PlainTV@, or returns @Nothing@
stripPlainTV_maybe :: TyVarBndr_ flag -> Maybe Name
stripPlainTV_maybe = elimTV Just (\_ _ -> Nothing)

-- | Report that a certain TH construct is impossible
impossible :: Fail.MonadFail q => String -> q a
impossible err = Fail.fail (err ++ "\n    This should not happen in Haskell.\n    Please email rae@cs.brynmawr.edu with your code if you see this.")

-- | Convert a 'TyVarBndr' into a 'Type', dropping the kind signature
-- (if it has one).
tvbToType :: TyVarBndr_ flag -> Type
tvbToType = VarT . tvName

-- | Convert a 'TyVarBndr' into a 'Type', preserving the kind signature
-- (if it has one).
tvbToTypeWithSig :: TyVarBndr_ flag -> Type
tvbToTypeWithSig = elimTV VarT (\n k -> SigT (VarT n) k)

-- | Convert a 'TyVarBndr' into a 'TypeArg' (specifically, a 'TANormal'),
-- preserving the kind signature (if it has one).
tvbToTANormalWithSig :: TyVarBndr_ flag -> TypeArg
tvbToTANormalWithSig = TANormal . tvbToTypeWithSig

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

-- | Extract the degree of an unboxed sum
unboxedSumDegree_maybe :: String -> Maybe Int
unboxedSumDegree_maybe = unboxedSumTupleDegree_maybe '|'

-- | Extract the degree of an unboxed sum name
unboxedSumNameDegree_maybe :: Name -> Maybe Int
unboxedSumNameDegree_maybe = unboxedSumDegree_maybe . nameBase

-- | Extract the degree of an unboxed tuple
unboxedTupleDegree_maybe :: String -> Maybe Int
unboxedTupleDegree_maybe = unboxedSumTupleDegree_maybe ','

-- | Extract the degree of an unboxed sum or tuple
unboxedSumTupleDegree_maybe :: Char -> String -> Maybe Int
unboxedSumTupleDegree_maybe sep s = do
  '(' : '#' : s1 <- return s
  (seps, "#)") <- return $ span (== sep) s1
  let degree
        | "" <- seps = 0
        | otherwise  = length seps + 1
  return degree

-- | Extract the degree of an unboxed tuple name
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

-- | The type variable binders in a @forall@. This is not used by the TH AST
-- itself, but this is used as an intermediate data type in 'FAForalls'.
data ForallTelescope
  = ForallVis [TyVarBndrUnit]
    -- ^ A visible @forall@ (e.g., @forall a -> {...}@).
    --   These do not have any notion of specificity, so we use
    --   '()' as a placeholder value in the 'TyVarBndr's.
  | ForallInvis [TyVarBndrSpec]
    -- ^ An invisible @forall@ (e.g., @forall a {b} c -> {...}@),
    --   where each binder has a 'Specificity'.
  deriving (Eq, Show, Typeable, Data)

-- | The list of arguments in a function 'Type'.
data FunArgs
  = FANil
    -- ^ No more arguments.
  | FAForalls ForallTelescope FunArgs
    -- ^ A series of @forall@ed type variables followed by a dot (if
    --   'ForallInvis') or an arrow (if 'ForallVis'). For example,
    --   the type variables @a1 ... an@ in @forall a1 ... an. r@.
  | FACxt Cxt FunArgs
    -- ^ A series of constraint arguments followed by @=>@. For example,
    --   the @(c1, ..., cn)@ in @(c1, ..., cn) => r@.
  | FAAnon Type FunArgs
    -- ^ An anonymous argument followed by an arrow. For example, the @a@
    --   in @a -> r@.
  deriving (Eq, Show, Typeable, Data)

-- | A /visible/ function argument type (i.e., one that must be supplied
-- explicitly in the source code). This is in contrast to /invisible/
-- arguments (e.g., the @c@ in @c => r@), which are instantiated without
-- the need for explicit user input.
data VisFunArg
  = VisFADep TyVarBndrUnit
    -- ^ A visible @forall@ (e.g., @forall a -> a@).
  | VisFAAnon Type
    -- ^ An anonymous argument followed by an arrow (e.g., @a -> r@).
  deriving (Eq, Show, Typeable, Data)

-- | Filter the visible function arguments from a list of 'FunArgs'.
filterVisFunArgs :: FunArgs -> [VisFunArg]
filterVisFunArgs FANil = []
filterVisFunArgs (FAForalls tele args) =
  case tele of
    ForallVis tvbs -> map VisFADep tvbs ++ args'
    ForallInvis _  -> args'
  where
    args' = filterVisFunArgs args
filterVisFunArgs (FACxt _ args) =
  filterVisFunArgs args
filterVisFunArgs (FAAnon t args) =
  VisFAAnon t:filterVisFunArgs args

-- | Reconstruct an arrow 'Type' from its argument and result types.
ravelType :: FunArgs -> Type -> Type
ravelType FANil res = res
-- We need a special case for FAForalls ForallInvis followed by FACxt so that we may
-- collapse them into a single ForallT when raveling.
-- See Note [Desugaring and sweetening ForallT] in L.H.T.Desugar.Core.
ravelType (FAForalls (ForallInvis tvbs) (FACxt p args)) res =
  ForallT tvbs p (ravelType args res)
ravelType (FAForalls (ForallInvis  tvbs)  args)  res = ForallT tvbs [] (ravelType args res)
ravelType (FAForalls (ForallVis   _tvbs) _args) _res =
#if __GLASGOW_HASKELL__ >= 809
      ForallVisT _tvbs (ravelType _args _res)
#else
      error "Visible dependent quantification supported only on GHC 8.10+"
#endif
ravelType (FACxt cxt args) res = ForallT [] cxt (ravelType args res)
ravelType (FAAnon t args)  res = AppT (AppT ArrowT t) (ravelType args res)

-- | Decompose a function 'Type' into its arguments (the 'FunArgs') and its
-- result type (the 'Type).
unravelType :: Type -> (FunArgs, Type)
unravelType (ForallT tvbs cxt ty) =
  let (args, res) = unravelType ty in
  (FAForalls (ForallInvis tvbs) (FACxt cxt args), res)
unravelType (AppT (AppT ArrowT t1) t2) =
  let (args, res) = unravelType t2 in
  (FAAnon t1 args, res)
#if __GLASGOW_HASKELL__ >= 809
unravelType (ForallVisT tvbs ty) =
  let (args, res) = unravelType ty in
  (FAForalls (ForallVis tvbs) args, res)
#endif
unravelType t = (FANil, t)

-- | Remove all of the explicit kind signatures from a 'Type'.
unSigType :: Type -> Type
unSigType (SigT t _) = t
unSigType (AppT f x) = AppT (unSigType f) (unSigType x)
unSigType (ForallT tvbs ctxt t) =
  ForallT tvbs (map unSigPred ctxt) (unSigType t)
#if __GLASGOW_HASKELL__ >= 800
unSigType (InfixT t1 n t2)  = InfixT (unSigType t1) n (unSigType t2)
unSigType (UInfixT t1 n t2) = UInfixT (unSigType t1) n (unSigType t2)
unSigType (ParensT t)       = ParensT (unSigType t)
#endif
#if __GLASGOW_HASKELL__ >= 807
unSigType (AppKindT t k)       = AppKindT (unSigType t) (unSigType k)
unSigType (ImplicitParamT n t) = ImplicitParamT n (unSigType t)
#endif
unSigType t = t

-- | Remove all of the explicit kind signatures from a 'Pred'.
unSigPred :: Pred -> Pred
#if __GLASGOW_HASKELL__ >= 710
unSigPred = unSigType
#else
unSigPred (ClassP n tys) = ClassP n (map unSigType tys)
unSigPred (EqualP t1 t2) = EqualP (unSigType t1) (unSigType t2)
#endif

-- | Decompose an applied type into its individual components. For example, this:
--
-- @
-- Proxy \@Type Char
-- @
--
-- would be unfolded to this:
--
-- @
-- ('ConT' ''Proxy, ['TyArg' ('ConT' ''Type), 'TANormal' ('ConT' ''Char)])
-- @
unfoldType :: Type -> (Type, [TypeArg])
unfoldType = go []
  where
    go :: [TypeArg] -> Type -> (Type, [TypeArg])
    go acc (ForallT _ _ ty) = go acc ty
    go acc (AppT ty1 ty2)   = go (TANormal ty2:acc) ty1
    go acc (SigT ty _)      = go acc ty
#if __GLASGOW_HASKELL__ >= 800
    go acc (ParensT ty)     = go acc ty
#endif
#if __GLASGOW_HASKELL__ >= 807
    go acc (AppKindT ty ki) = go (TyArg ki:acc) ty
#endif
    go acc ty               = (ty, acc)

-- | An argument to a type, either a normal type ('TANormal') or a visible
-- kind application ('TyArg').
--
-- 'TypeArg' is useful when decomposing an application of a 'Type' to its
-- arguments (e.g., in 'unfoldType').
data TypeArg
  = TANormal Type
  | TyArg Kind
  deriving (Eq, Show, Typeable, Data)

-- | Apply one 'Type' to a list of arguments.
applyType :: Type -> [TypeArg] -> Type
applyType = foldl apply
  where
    apply :: Type -> TypeArg -> Type
    apply f (TANormal x) = f `AppT` x
    apply f (TyArg _x)   =
#if __GLASGOW_HASKELL__ >= 807
                           f `AppKindT` _x
#else
                           -- VKA isn't supported, so
                           -- conservatively drop the argument
                           f
#endif

-- | Filter the normal type arguments from a list of 'TypeArg's.
filterTANormals :: [TypeArg] -> [Type]
filterTANormals = mapMaybe getTANormal
  where
    getTANormal :: TypeArg -> Maybe Type
    getTANormal (TANormal t) = Just t
    getTANormal (TyArg {})   = Nothing

-- | Extract the underlying 'Type' or 'Kind' from a 'TypeArg'. This forgets
-- information about whether a type is a normal argument or not, so use with
-- caution.
probablyWrongUnTypeArg :: TypeArg -> Type
probablyWrongUnTypeArg (TANormal t) = t
probablyWrongUnTypeArg (TyArg k)    = k

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
extractBoundNamesStmt :: Stmt -> OSet Name
extractBoundNamesStmt (BindS pat _) = extractBoundNamesPat pat
extractBoundNamesStmt (LetS decs)   = foldMap extractBoundNamesDec decs
extractBoundNamesStmt (NoBindS _)   = OS.empty
extractBoundNamesStmt (ParS stmtss) = foldMap (foldMap extractBoundNamesStmt) stmtss
#if __GLASGOW_HASKELL__ >= 807
extractBoundNamesStmt (RecS stmtss) = foldMap extractBoundNamesStmt stmtss
#endif

-- | Extract the names bound in a @Dec@ that could appear in a @let@ expression.
extractBoundNamesDec :: Dec -> OSet Name
extractBoundNamesDec (FunD name _)  = OS.singleton name
extractBoundNamesDec (ValD pat _ _) = extractBoundNamesPat pat
extractBoundNamesDec _              = OS.empty

-- | Extract the names bound in a @Pat@
extractBoundNamesPat :: Pat -> OSet Name
extractBoundNamesPat (LitP _)              = OS.empty
extractBoundNamesPat (VarP name)           = OS.singleton name
extractBoundNamesPat (TupP pats)           = foldMap extractBoundNamesPat pats
extractBoundNamesPat (UnboxedTupP pats)    = foldMap extractBoundNamesPat pats
extractBoundNamesPat (ConP _ pats)         = foldMap extractBoundNamesPat pats
extractBoundNamesPat (InfixP p1 _ p2)      = extractBoundNamesPat p1 `OS.union`
                                             extractBoundNamesPat p2
extractBoundNamesPat (UInfixP p1 _ p2)     = extractBoundNamesPat p1 `OS.union`
                                             extractBoundNamesPat p2
extractBoundNamesPat (ParensP pat)         = extractBoundNamesPat pat
extractBoundNamesPat (TildeP pat)          = extractBoundNamesPat pat
extractBoundNamesPat (BangP pat)           = extractBoundNamesPat pat
extractBoundNamesPat (AsP name pat)        = OS.singleton name `OS.union`
                                             extractBoundNamesPat pat
extractBoundNamesPat WildP                 = OS.empty
extractBoundNamesPat (RecP _ field_pats)   = let (_, pats) = unzip field_pats in
                                             foldMap extractBoundNamesPat pats
extractBoundNamesPat (ListP pats)          = foldMap extractBoundNamesPat pats
extractBoundNamesPat (SigP pat _)          = extractBoundNamesPat pat
extractBoundNamesPat (ViewP _ pat)         = extractBoundNamesPat pat
#if __GLASGOW_HASKELL__ >= 801
extractBoundNamesPat (UnboxedSumP pat _ _) = extractBoundNamesPat pat
#endif

----------------------------------------
-- General utility
----------------------------------------

#if __GLASGOW_HASKELL__ >= 800
-- dirty implementation of explicit-to-implicit conversion
newtype MagicIP name a r = MagicIP (IP name a => r)

-- | Get an implicit param constraint (@IP name a@, which is the desugared
-- form of @(?name :: a)@) from an explicit value.
--
-- This function is only available with GHC 8.0 or later.
bindIP :: forall name a r. a -> (IP name a => r) -> r
bindIP val k = (unsafeCoerce (MagicIP @name k) :: a -> r) val
#endif

-- like GHC's
splitAtList :: [a] -> [b] -> ([b], [b])
splitAtList [] x = ([], x)
splitAtList (_ : t) (x : xs) =
  let (as, bs) = splitAtList t xs in
  (x : as, bs)
splitAtList (_ : _) [] = ([], [])

thdOf3 :: (a,b,c) -> c
thdOf3 (_,_,c) = c

liftFst :: (a -> b) -> (a, c) -> (b, c)
liftFst f (a,c) = (f a, c)

liftSnd :: (a -> b) -> (c, a) -> (c, b)
liftSnd f (c,a) = (c, f a)

thirdOf3 :: (a -> b) -> (c, d, a) -> (c, d, b)
thirdOf3 f (c, d, a) = (c, d, f a)

-- lift concatMap into a monad
-- could this be more efficient?
-- | Concatenate the result of a @mapM@
concatMapM :: (Monad monad, Monoid monoid, Traversable t)
           => (a -> monad monoid) -> t a -> monad monoid
concatMapM fn list = do
  bss <- mapM fn list
  return $ fold bss

-- like GHC's
-- | Monadic version of mapAccumL
mapAccumLM :: Monad m
            => (acc -> x -> m (acc, y)) -- ^ combining function
            -> acc                      -- ^ initial state
            -> [x]                      -- ^ inputs
            -> m (acc, [y])             -- ^ final state, outputs
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
    (s1, x')  <- f s x
    (s2, xs') <- mapAccumLM f s1 xs
    return    (s2, x' : xs')

-- like GHC's
mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM _ [] = return []
mapMaybeM f (x:xs) = do
  y <- f x
  ys <- mapMaybeM f xs
  return $ case y of
    Nothing -> ys
    Just z  -> z : ys

expectJustM :: Fail.MonadFail m => String -> Maybe a -> m a
expectJustM _   (Just x) = return x
expectJustM err Nothing  = Fail.fail err

firstMatch :: (a -> Maybe b) -> [a] -> Maybe b
firstMatch f xs = listToMaybe $ mapMaybe f xs

-- | Semi-shallow version of 'everywhereM' - does not recurse into children of nodes of type @a@ (only applies the handler to them).
--
-- >>> topEverywhereM (pure . fmap (*10) :: [Integer] -> Identity [Integer]) ([1,2,3] :: [Integer], "foo" :: String)
-- Identity ([10,20,30],"foo")
--
-- >>> everywhereM (mkM (pure . fmap (*10) :: [Integer] -> Identity [Integer])) ([1,2,3] :: [Integer], "foo" :: String)
-- Identity ([10,200,3000],"foo")
topEverywhereM :: (Typeable a, Data b, Monad m) => (a -> m a) -> b -> m b
topEverywhereM handler =
  gmapM (topEverywhereM handler) `extM` handler

-- Checks if a String names a valid Haskell infix data constructor
-- (i.e., does it begin with a colon?).
isInfixDataCon :: String -> Bool
isInfixDataCon (':':_) = True
isInfixDataCon _ = False

-- | Returns 'True' if the argument 'Name' is that of 'Kind.Type'
-- (or @*@ or 'Kind.★', to support older GHCs).
isTypeKindName :: Name -> Bool
isTypeKindName n = n == typeKindName
#if __GLASGOW_HASKELL__ < 805
                || n == starKindName
                || n == uniStarKindName
#endif

-- | The 'Name' of:
--
-- 1. The kind 'Kind.Type', on GHC 8.0 or later.
-- 2. The kind @*@ on older GHCs.
typeKindName :: Name
#if __GLASGOW_HASKELL__ >= 800
typeKindName = ''Kind.Type
#else
typeKindName = starKindName
#endif

#if __GLASGOW_HASKELL__ < 805
-- | The 'Name' of the kind @*@.
starKindName :: Name
#if __GLASGOW_HASKELL__ >= 800
starKindName = ''(Kind.*)
#else
starKindName = mkNameG_tc "ghc-prim" "GHC.Prim" "*"
#endif

-- | The 'Name' of:
--
-- 1. The kind 'Kind.★', on GHC 8.0 or later.
-- 2. The kind @*@ on older GHCs.
uniStarKindName :: Name
#if __GLASGOW_HASKELL__ >= 800
uniStarKindName = ''(Kind.★)
#else
uniStarKindName = starKindName
#endif
#endif
