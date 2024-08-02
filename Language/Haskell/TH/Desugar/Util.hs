{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Utility functions for th-desugar package.
-}

{-# LANGUAGE CPP, DeriveDataTypeable, DeriveGeneric, DeriveLift, RankNTypes,
             ScopedTypeVariables, TupleSections, AllowAmbiguousTypes,
             TemplateHaskellQuotes, TypeApplications, MagicHash #-}

module Language.Haskell.TH.Desugar.Util (
  newUniqueName,
  impossible,
  nameOccursIn, allNamesIn, mkTypeName, mkDataName, mkNameWith, isDataName,
  stripVarP_maybe, extractBoundNamesStmt,
  concatMapM, mapAccumLM, mapMaybeM, expectJustM,
  stripPlainTV_maybe, extractTvbKind_maybe,
  thirdOf3, splitAtList, extractBoundNamesDec,
  extractBoundNamesPat,
  tvbToType, tvbToTypeWithSig,
  nameMatches, thdOf3, liftFst, liftSnd, firstMatch, firstMatchM,
  tupleNameDegree_maybe,
  unboxedSumNameDegree_maybe, unboxedTupleNameDegree_maybe, splitTuple_maybe,
  topEverywhereM, isInfixDataCon,
  isTypeKindName, typeKindName,
  unSigType, unfoldType, ForallTelescope(..), FunArgs(..), VisFunArg(..),
  filterVisFunArgs, ravelType, unravelType,
  TypeArg(..), applyType, filterTANormals, probablyWrongUnTypeArg,
  tyVarBndrVisToTypeArg, tyVarBndrVisToTypeArgWithSig,
  bindIP,
  DataFlavor(..),
  freeKindVariablesWellScoped,
  ForAllTyFlag(..), tvbForAllTyFlagsToSpecs, tvbForAllTyFlagsToBndrVis,
  matchUpSAKWithDecl
  ) where

import Prelude hiding (mapM, foldl, concatMap, any)

import Language.Haskell.TH hiding ( cxt )
import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Datatype.TyVarBndr
import qualified Language.Haskell.TH.Desugar.OSet as OS
import Language.Haskell.TH.Desugar.OSet (OSet)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax

import qualified Control.Monad.Fail as Fail
import Data.Foldable
import Data.Function ( on )
import Data.Generics ( Data, Typeable, everything, extM, gmapM, mkQ )
import qualified Data.Kind as Kind
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Maybe
import qualified Data.Set as Set
import Data.Traversable
import GHC.Classes ( IP )
import GHC.Generics ( Generic )
import Unsafe.Coerce ( unsafeCoerce )

#if __GLASGOW_HASKELL__ >= 900
import Language.Haskell.TH.Ppr ( PprFlag(..) )
import qualified Language.Haskell.TH.PprLib as Ppr
#endif

#if __GLASGOW_HASKELL__ >= 906
import GHC.Tuple ( Solo(MkSolo) )
#elif __GLASGOW_HASKELL__ >= 900
import GHC.Tuple ( Solo(Solo) )
#endif

#if __GLASGOW_HASKELL__ >= 908
import GHC.Tuple ( Tuple0, Unit )
import Text.Read ( readMaybe )
#endif

#if __GLASGOW_HASKELL__ >= 910
import GHC.Types ( Solo#, Sum2#, Tuple0#, Unit# )
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

-- | Extracts the kind from a 'TyVarBndr'. Returns @'Just' k@ if the 'TyVarBndr'
-- is a 'KindedTV' and returns 'Nothing' if it is a 'PlainTV'.
extractTvbKind_maybe :: TyVarBndr_ flag -> Maybe Kind
extractTvbKind_maybe = elimTV (\_ -> Nothing) (\_ k -> Just k)

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

-- | Extract the degree of a tuple 'Name'.
--
-- In addition to recognizing tuple syntax (e.g., @''(,,)@), this also
-- recognizes the following:
--
-- * @''Unit@ (for 0-tuples)
--
-- * @''Solo@/@'MkSolo@ (for 1-tuples)
--
-- * @''Tuple<N>@ (for <N>-tuples)
--
-- In recent versions of GHC, @''()@ is a synonym for @''Unit@, @''(,)@ is a
-- synonym for @''Tuple2@, and so on. As a result, we must check for @''Unit@
-- and @''Tuple<N>@ in 'tupleDegree_maybe' to be thorough. (There is no special
-- tuple syntax for @''Solo@/@'MkSolo@, but we check them here as well for the
-- sake of completeness.)
tupleNameDegree_maybe :: Name -> Maybe Int
tupleNameDegree_maybe name
  -- First, check for Solo/MkSolo...
#if __GLASGOW_HASKELL__ >= 900
  | name == ''Solo = Just 1
#if __GLASGOW_HASKELL__ >= 906
  | name == 'MkSolo = Just 1
#else
  | name == 'Solo = Just 1
#endif
#endif
#if __GLASGOW_HASKELL__ >= 908
  -- ...then, check for Unit...
  | name == ''Unit = Just 0
  -- ...then, check for Tuple<N>. It is theoretically possible for the supplied
  -- Name to be a user-defined data type named Tuple<N>, rather than the actual
  -- tuple types defined in GHC.Tuple. As such, we check that the package and
  -- module for the supplied Name does in fact come from ghc-prim:GHC.Tuple as
  -- a sanity check.
  | -- We use Tuple0 here simply because it is a convenient identifier from
    -- GHC.Tuple. We could just as well use any other identifier from GHC.Tuple,
    -- however.
    namePackage name == namePackage ''Tuple0
  , nameModule name == nameModule ''Tuple0
  , 'T':'u':'p':'l':'e':n <- nameBase name
    -- This relies on the Read Int instance. This is more permissive than what
    -- we need, since there are valid Int strings (e.g., "-1") that do not have
    -- corresponding Tuple<N> names (e.g., "Tuple-1" is not a data type in
    -- GHC.Tuple). As such, we depend on the assumption that the input string
    -- does in fact come from GHC.Tuple, which we check above.
  = readMaybe n
#endif
  -- ...otherwise, fall back on tuple syntax.
  | otherwise
  = tuple_syntax_degree_maybe (nameBase name)
  where
    -- Extract the degree of a string using tuple syntax (e.g., @''(,,)@).
    tuple_syntax_degree_maybe :: String -> Maybe Int
    tuple_syntax_degree_maybe s = do
      '(' : s1 <- return s
      (commas, ")") <- return $ span (== ',') s1
      let degree
            | "" <- commas = 0
            | otherwise    = length commas + 1
      return degree

-- | Extract the degree of an unboxed sum
unboxedSumDegree_maybe :: String -> Maybe Int
unboxedSumDegree_maybe = unboxedSumTupleDegree_maybe '|'

-- | Extract the degree of an unboxed sum 'Name'.
--
-- In addition to recognizing unboxed sum syntax (e.g., @''(#||#)@), this also
-- recognizes @''Sum<N>#@ (for unboxed <N>-ary sum type constructors). In recent
-- versions of GHC, @''Sum2#@ is a synonym for @''(#|#)@, @''Sum3#@ is a synonym
-- for @''(#||#)@, and so on. As a result, we must check for @''Sum<N>#@ in
-- 'unboxedSumNameDegree_maybe' to be thorough.
unboxedSumNameDegree_maybe :: Name -> Maybe Int
unboxedSumNameDegree_maybe name
#if __GLASGOW_HASKELL__ >= 910
  -- Check for Sum<N>#. It is theoretically possible for the supplied
  -- Name to be a user-defined data type named Sum<N>#, rather than the actual
  -- unboxed sum types defined in GHC.Types. As such, we check that the package
  -- and module for the supplied Name does in fact come from ghc-prim:GHC.Types
  -- as a sanity check.
  | -- We use Sum2# here simply because it is a convenient identifier from
    -- GHC.Types. We could just as well use any other identifier from GHC.Types,
    -- however.
    namePackage name == namePackage ''Sum2#
  , nameModule name == nameModule ''Sum2#
  , 'S':'u':'m':n:"#" <- nameBase name
    -- This relies on the Read Int instance. This is more permissive than what
    -- we need, since there are valid Int strings (e.g., "-1") that do not have
    -- corresponding Sum<N># names (e.g., "Sum-1#" is not a data type in
    -- GHC.Types). As such, we depend on the assumption that the input string
    -- does in fact come from GHC.Types, which we check above.
  = readMaybe [n]
#endif
  -- ...otherwise, fall back on unboxed sum syntax.
  | otherwise
  = unboxedSumDegree_maybe (nameBase name)

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

-- | Extract the degree of an unboxed tuple 'Name'.
--
-- In addition to recognizing unboxed tuple syntax (e.g., @''(#,,#)@), this also
-- recognizes the following:
--
-- * @''Unit#@ (for unboxed 0-tuples)
--
-- * @''Solo#@/@'Solo#@ (for unboxed 1-tuples)
--
-- * @''Tuple<N>#@ (for unboxed <N>-tuples)
--
-- In recent versions of GHC, @''(##)@ is a synonym for @''Unit#@, @''(#,#)@ is
-- a synonym for @''Tuple2#@, and so on. As a result, we must check for
-- @''Unit#@, and @''Tuple<N>@ in 'unboxedTupleNameDegree_maybe' to be thorough.
-- (There is no special unboxed tuple type constructor for @''Solo#@/@'Solo#@,
-- but we check them here as well for the sake of completeness.)
unboxedTupleNameDegree_maybe :: Name -> Maybe Int
unboxedTupleNameDegree_maybe name
#if __GLASGOW_HASKELL__ >= 910
  -- First, check for Solo#...
  | name == ''Solo# = Just 1
  -- ...then, check for Unit#...
  | name == ''Unit# = Just 0
  -- ...then, check for Tuple<N>#. It is theoretically possible for the supplied
  -- Name to be a user-defined data type named Tuple<N>#, rather than the actual
  -- unboxed tuple types defined in GHC.Types. As such, we check that the
  -- package and module for the supplied Name does in fact come from
  -- ghc-prim:GHC.Types as a sanity check.
  | -- We use Tuple0# here simply because it is a convenient identifier from
    -- GHC.Types. We could just as well use any other identifier from GHC.Types,
    -- however.
    namePackage name == namePackage ''Tuple0#
  , nameModule name == nameModule ''Tuple0#
  , 'T':'u':'p':'l':'e':n:"#" <- nameBase name
    -- This relies on the Read Int instance. This is more permissive than what
    -- we need, since there are valid Int strings (e.g., "-1") that do not have
    -- corresponding Tuple<N># names (e.g., "Tuple-1#" is not a data type in
    -- GHC.Types). As such, we depend on the assumption that the input string
    -- does in fact come from GHC.Types, which we check above.
  = readMaybe [n]
#endif
  -- ...otherwise, fall back on unboxed tuple syntax.
  | otherwise
  = unboxedTupleDegree_maybe (nameBase name)

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
  deriving (Eq, Show, Data)

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
  deriving (Eq, Show, Data)

-- | A /visible/ function argument type (i.e., one that must be supplied
-- explicitly in the source code). This is in contrast to /invisible/
-- arguments (e.g., the @c@ in @c => r@), which are instantiated without
-- the need for explicit user input.
data VisFunArg
  = VisFADep TyVarBndrUnit
    -- ^ A visible @forall@ (e.g., @forall a -> a@).
  | VisFAAnon Type
    -- ^ An anonymous argument followed by an arrow (e.g., @a -> r@).
  deriving (Eq, Show, Data)

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
unSigType (InfixT t1 n t2)  = InfixT (unSigType t1) n (unSigType t2)
unSigType (UInfixT t1 n t2) = UInfixT (unSigType t1) n (unSigType t2)
unSigType (ParensT t)       = ParensT (unSigType t)
#if __GLASGOW_HASKELL__ >= 807
unSigType (AppKindT t k)       = AppKindT (unSigType t) (unSigType k)
unSigType (ImplicitParamT n t) = ImplicitParamT n (unSigType t)
#endif
unSigType t = t

-- | Remove all of the explicit kind signatures from a 'Pred'.
unSigPred :: Pred -> Pred
unSigPred = unSigType

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
--
-- This process forgets about infix application, so both of these types:
--
-- @
-- Int :++: Int
-- (:++:) Int Int
-- @
--
-- will be unfolded to this:
--
-- @
-- ('ConT' ''(:+:), ['TANormal' ('ConT' ''Int), 'TANormal' ('ConT' ''Int)])
-- @
--
-- This function should only be used after all 'UInfixT' and 'PromotedUInfixT'
-- types have been resolved (e.g., via @th-abstraction@'s
-- @<https://hackage.haskell.org/package/th-abstraction-0.5.0.0/docs/Language-Haskell-TH-Datatype.html#v:resolveInfixT resolveInfixT>@
-- function).
unfoldType :: Type -> (Type, [TypeArg])
unfoldType = go []
  where
    go :: [TypeArg] -> Type -> (Type, [TypeArg])
    go acc (ForallT _ _ ty)           = go acc ty
    go acc (AppT ty1 ty2)             = go (TANormal ty2:acc) ty1
    go acc (SigT ty _)                = go acc ty
    go acc (ParensT ty)               = go acc ty
    go acc (InfixT ty1 n ty2)         = go (TANormal ty1:TANormal ty2:acc) (ConT n)
#if __GLASGOW_HASKELL__ >= 807
    go acc (AppKindT ty ki)           = go (TyArg ki:acc) ty
#endif
#if __GLASGOW_HASKELL__ >= 904
    go acc (PromotedInfixT ty1 n ty2) = go (TANormal ty1:TANormal ty2:acc) (PromotedT n)
#endif
    go acc ty                         = (ty, acc)

-- | An argument to a type, either a normal type ('TANormal') or a visible
-- kind application ('TyArg').
--
-- 'TypeArg' is useful when decomposing an application of a 'Type' to its
-- arguments (e.g., in 'unfoldType').
data TypeArg
  = TANormal Type
  | TyArg Kind
  deriving (Eq, Show, Data)

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

-- | Convert a 'TyVarBndrVis' to a 'TypeArg'. That is, convert a binder with a
-- 'BndrReq' visibility to a 'TANormal' and a binder with 'BndrInvis'
-- visibility to a 'TyArg'.
--
-- If given a 'KindedTV', the resulting 'TypeArg' will omit the kind signature.
-- Use 'tyVarBndrVisToTypeArgWithSig' if you want to preserve the kind
-- signature.
tyVarBndrVisToTypeArg :: TyVarBndrVis -> TypeArg
tyVarBndrVisToTypeArg bndr =
  case tvFlag bndr of
    BndrReq   -> TANormal bndr_ty
    BndrInvis -> TyArg bndr_ty
  where
    bndr_ty = tvbToType bndr

-- | Convert a 'TyVarBndrVis' to a 'TypeArg'. That is, convert a binder with a
-- 'BndrReq' visibility to a 'TANormal' and a binder with 'BndrInvis'
-- visibility to a 'TyArg'.
--
-- If given a 'KindedTV', the resulting 'TypeArg' will preserve the kind
-- signature. Use 'tyVarBndrVisToTypeArg' if you want to omit the kind
-- signature.
tyVarBndrVisToTypeArgWithSig :: TyVarBndrVis -> TypeArg
tyVarBndrVisToTypeArgWithSig bndr =
  case tvFlag bndr of
    BndrReq   -> TANormal bndr_ty
    BndrInvis -> TyArg bndr_ty
  where
    bndr_ty = tvbToTypeWithSig bndr

-- | Extract the underlying 'Type' or 'Kind' from a 'TypeArg'. This forgets
-- information about whether a type is a normal argument or not, so use with
-- caution.
probablyWrongUnTypeArg :: TypeArg -> Type
probablyWrongUnTypeArg (TANormal t) = t
probablyWrongUnTypeArg (TyArg k)    = k

-------------------------------------------------------------------------------
-- Matching standalone kind signatures with binders in type-level declarations
-------------------------------------------------------------------------------

-- @'matchUpSAKWithDecl' decl_sak decl_bndrs@ produces @TyVarBndr'
-- 'ForAllTyFlag'@s for a declaration, using the original declaration's
-- standalone kind signature (@decl_sak@) and its user-written binders
-- (@decl_bndrs@) as a template. For this example:
--
-- @
-- type D :: forall j k. k -> j -> Type
-- data D \@j \@l (a :: l) b = ...
-- @
--
-- We would produce the following @'TyVarBndr' 'ForAllTyFlag'@s:
--
-- @
-- \@j \@l (a :: l) (b :: j)
-- @
--
-- From here, these @'TyVarBndr' 'ForAllTyFlag'@s can be converted into other
-- forms of 'TyVarBndr's:
--
-- * They can be converted to 'TyVarBndrSpec's using 'tvbForAllTyFlagsToSpecs'.
--
-- * They can be converted to 'TyVarBndrVis'es using 'tvbForAllTyFlagsToVis'.
--
-- Note that:
--
-- * This function has a precondition that the length of @decl_bndrs@ must
--   always be equal to the number of visible quantifiers (i.e., the number of
--   function arrows plus the number of visible @forall@–bound variables) in
--   @decl_sak@.
--
-- * Whenever possible, this function reuses type variable names from the
--   declaration's user-written binders. This is why the @'TyVarBndr'
--   'ForAllTyFlag'@ use @\@j \@l@ instead of @\@j \@k@, since the @(a :: l)@
--   binder uses @l@ instead of @k@. We could have just as well chose the other
--   way around, but we chose to pick variable names from the user-written
--   binders since they scope over other parts of the declaration. (For example,
--   the user-written binders of a @data@ declaration scope over the type
--   variables mentioned in a @deriving@ clause.) As such, keeping these names
--   avoids having to perform some alpha-renaming.
--
-- This function's implementation was heavily inspired by parts of GHC's
-- kcCheckDeclHeader_sig function:
-- https://gitlab.haskell.org/ghc/ghc/-/blob/1464a2a8de082f66ae250d63ab9d94dbe2ef8620/compiler/GHC/Tc/Gen/HsType.hs#L2524-2643
matchUpSAKWithDecl ::
     forall q.
     Fail.MonadFail q
  => Kind
     -- ^ The declaration's standalone kind signature
  -> [TyVarBndrVis]
     -- ^ The user-written binders in the declaration
  -> q [TyVarBndr_ ForAllTyFlag]
matchUpSAKWithDecl decl_sak decl_bndrs = do
  -- (1) First, explicitly quantify any free kind variables in `decl_sak` using
  -- an invisible @forall@. This is done to ensure that precondition (2) in
  -- `matchUpSigWithDecl` is upheld. (See the Haddocks for that function).
  let decl_sak_free_tvbs =
        changeTVFlags SpecifiedSpec $ freeVariablesWellScoped [decl_sak]
      decl_sak' = ForallT decl_sak_free_tvbs [] decl_sak

  -- (2) Next, compute type variable binders using `matchUpSigWithDecl`. Note
  -- that these can be biased towards type variable names mention in `decl_sak`
  -- over names mentioned in `decl_bndrs`, but we will fix that up in the next
  -- step.
  let (decl_sak_args, _) = unravelType decl_sak'
  sing_sak_tvbs <- matchUpSigWithDecl decl_sak_args decl_bndrs

  -- (3) Finally, swizzle the type variable names so that names in `decl_bndrs`
  -- are preferred over names in `decl_sak`.
  --
  -- This is heavily inspired by similar code in GHC:
  -- https://gitlab.haskell.org/ghc/ghc/-/blob/cec903899234bf9e25ea404477ba846ac1e963bb/compiler/GHC/Tc/Gen/HsType.hs#L2607-2616
  let invis_decl_sak_args = filterInvisTvbArgs decl_sak_args
      invis_decl_sak_arg_nms = map tvName invis_decl_sak_args

      invis_decl_bndrs = freeKindVariablesWellScoped decl_bndrs
      invis_decl_bndr_nms = map tvName invis_decl_bndrs

      swizzle_env =
        Map.fromList $ zip invis_decl_sak_arg_nms invis_decl_bndr_nms
      (_, swizzled_sing_sak_tvbs) =
        List.mapAccumL (swizzleTvb swizzle_env) Map.empty sing_sak_tvbs
  pure swizzled_sing_sak_tvbs

-- Match the quantifiers in a type-level declaration's standalone kind signature
-- with the user-written binders in the declaration. This function assumes the
-- following preconditions:
--
-- 1. The number of required binders in the declaration's user-written binders
--    is equal to the number of visible quantifiers (i.e., the number of
--    function arrows plus the number of visible @forall@–bound variables) in
--    the standalone kind signature.
--
-- 2. The number of invisible \@-binders in the declaration's user-written
--    binders is less than or equal to the number of invisible quantifiers
--    (i.e., the number of invisible @forall@–bound variables) in the
--    standalone kind signature.
--
-- The implementation of this function is heavily based on a GHC function of
-- the same name:
-- https://gitlab.haskell.org/ghc/ghc/-/blob/1464a2a8de082f66ae250d63ab9d94dbe2ef8620/compiler/GHC/Tc/Gen/HsType.hs#L2645-2715
matchUpSigWithDecl ::
     forall q.
     Fail.MonadFail q
  => FunArgs
     -- ^ The quantifiers in the declaration's standalone kind signature
  -> [TyVarBndrVis]
     -- ^ The user-written binders in the declaration
  -> q [TyVarBndr_ ForAllTyFlag]
matchUpSigWithDecl = go_fun_args Map.empty
  where
    go_fun_args ::
         Map Name Type
         -- ^ A substitution from the names of @forall@-bound variables in the
         -- standalone kind signature to corresponding binder names in the
         -- user-written binders. This is because we want to reuse type variable
         -- names from the user-written binders whenever possible. For example:
         --
         -- @
         -- type T :: forall a. forall b -> Maybe (a, b) -> Type
         -- data T @x y z
         -- @
         --
         -- After matching up the @a@ in @forall a.@ with @x@ and
         -- the @b@ in @forall b ->@ with @y@, this substitution will be
         -- extended with @[a :-> x, b :-> y]@. This ensures that we will
         -- produce @Maybe (x, y)@ instead of @Maybe (a, b)@ in
         -- the kind for @z@.
      -> FunArgs -> [TyVarBndrVis] -> q [TyVarBndr_ ForAllTyFlag]
    go_fun_args _ FANil [] =
      pure []
    -- This should not happen, per precondition (1).
    go_fun_args _ FANil decl_bndrs =
      fail $ "matchUpSigWithDecl.go_fun_args: Too many binders: " ++ show decl_bndrs
    -- GHC now disallows kind-level constraints, per this GHC proposal:
    -- https://github.com/ghc-proposals/ghc-proposals/blob/b0687d96ce8007294173b7f628042ac4260cc738/proposals/0547-no-kind-equalities.rst
    -- As such, we reject non-empty kind contexts. Empty contexts (which are
    -- benign) can sometimes arise due to @ForallT@, so we add a special case
    -- to allow them.
    go_fun_args subst (FACxt [] args) decl_bndrs =
      go_fun_args subst args decl_bndrs
    go_fun_args _ (FACxt (_:_) _) _ =
      fail "matchUpSigWithDecl.go_fun_args: Unexpected kind-level constraint"
    go_fun_args subst (FAForalls (ForallInvis tvbs) sig_args) decl_bndrs =
      go_invis_tvbs subst tvbs sig_args decl_bndrs
    go_fun_args subst (FAForalls (ForallVis tvbs) sig_args) decl_bndrs =
      go_vis_tvbs subst tvbs sig_args decl_bndrs
    go_fun_args subst (FAAnon anon sig_args) (decl_bndr:decl_bndrs) =
      case tvFlag decl_bndr of
        -- If the next decl_bndr is required, then we must match its kind (if
        -- one is provided) against the anonymous kind argument.
        BndrReq -> do
          let decl_bndr_name = tvName decl_bndr
              mb_decl_bndr_kind = extractTvbKind_maybe decl_bndr
              anon' = applySubstitution subst anon

              anon'' =
                case mb_decl_bndr_kind of
                  Nothing -> anon'
                  Just decl_bndr_kind -> do
                    let mb_match_subst = matchTy decl_bndr_kind anon'
                    maybe decl_bndr_kind (`applySubstitution` decl_bndr_kind) mb_match_subst
          sig_args' <- go_fun_args subst sig_args decl_bndrs
          pure $ kindedTVFlag decl_bndr_name Required anon'' : sig_args'
        -- We have a visible, anonymous argument in the kind, but an invisible
        -- @-binder as the next decl_bndr. This is ill kinded, so throw an
        -- error.
        --
        -- This should not happen, per precondition (2).
        BndrInvis ->
          fail $ "dMatchUpSigWithDecl.go_fun_args: Expected visible binder, encountered invisible binder: "
              ++ show decl_bndr
    -- This should not happen, per precondition (1).
    go_fun_args _ _ [] =
      fail "matchUpSigWithDecl.go_fun_args: Too few binders"

    go_invis_tvbs ::
         Map Name Type
      -> [TyVarBndrSpec]
      -> FunArgs
      -> [TyVarBndrVis]
      -> q [TyVarBndr_ ForAllTyFlag]
    go_invis_tvbs subst [] sig_args decl_bndrs =
      go_fun_args subst sig_args decl_bndrs
    go_invis_tvbs subst (invis_tvb:invis_tvbs) sig_args decl_bndrss =
      case decl_bndrss of
        [] -> skip_invis_bndr
        decl_bndr:decl_bndrs ->
          case tvFlag decl_bndr of
            BndrReq -> skip_invis_bndr
            -- If the next decl_bndr is an invisible @-binder, then we must match it
            -- against the invisible forall–bound variable in the kind.
            BndrInvis -> do
              let (subst', sig_tvb) = match_tvbs subst invis_tvb decl_bndr
              sig_args' <- go_invis_tvbs subst' invis_tvbs sig_args decl_bndrs
              pure (mapTVFlag Invisible sig_tvb : sig_args')
      where
        -- There is an invisible forall in the kind without a corresponding
        -- invisible @-binder, which is allowed. In this case, we simply apply
        -- the substitution and recurse.
        skip_invis_bndr :: q [TyVarBndr_ ForAllTyFlag]
        skip_invis_bndr = do
          let (subst', invis_tvb') = substTvb subst invis_tvb
          sig_args' <- go_invis_tvbs subst' invis_tvbs sig_args decl_bndrss
          pure $ mapTVFlag Invisible invis_tvb' : sig_args'

    go_vis_tvbs ::
         Map Name Type
      -> [TyVarBndrUnit]
      -> FunArgs
      -> [TyVarBndrVis]
      -> q [TyVarBndr_ ForAllTyFlag]
    go_vis_tvbs subst [] sig_args decl_bndrs =
      go_fun_args subst sig_args decl_bndrs
    -- This should not happen, per precondition (1).
    go_vis_tvbs _ (_:_) _ [] =
      fail "matchUpSigWithDecl.go_vis_tvbs: Too few binders"
    go_vis_tvbs subst (vis_tvb:vis_tvbs) sig_args (decl_bndr:decl_bndrs) = do
      case tvFlag decl_bndr of
        -- If the next decl_bndr is required, then we must match it against the
        -- visible forall–bound variable in the kind.
        BndrReq -> do
          let (subst', sig_tvb) = match_tvbs subst vis_tvb decl_bndr
          sig_args' <- go_vis_tvbs subst' vis_tvbs sig_args decl_bndrs
          pure (mapTVFlag (const Required) sig_tvb : sig_args')
        -- We have a visible forall in the kind, but an invisible @-binder as
        -- the next decl_bndr. This is ill kinded, so throw an error.
        --
        -- This should not happen, per precondition (2).
        BndrInvis ->
          fail $ "matchUpSigWithDecl.go_vis_tvbs: Expected visible binder, encountered invisible binder: "
              ++ show decl_bndr

    -- @match_tvbs subst sig_tvb decl_bndr@ will match the kind of @decl_bndr@
    -- against the kind of @sig_tvb@ to produce a new kind. This function
    -- produces two values as output:
    --
    -- 1. A new @subst@ that has been extended such that the name of @sig_tvb@
    --    maps to the name of @decl_bndr@. (See the Haddocks for the @Map Name
    --    Type@ argument to @go_fun_args@ for an explanation of why we do this.)
    --
    -- 2. A 'TyVarBndrSpec' that has the name of @decl_bndr@, but with the new
    --    kind resulting from matching.
    match_tvbs ::
         Map Name Type
      -> TyVarBndr_ flag
      -> TyVarBndrVis
      -> (Map Name Type, TyVarBndr_ flag)
    match_tvbs subst sig_tvb decl_bndr =
      let decl_bndr_name = tvName decl_bndr
          mb_decl_bndr_kind = extractTvbKind_maybe decl_bndr

          sig_tvb_name = tvName sig_tvb
          sig_tvb_flag = tvFlag sig_tvb
          mb_sig_tvb_kind = applySubstitution subst <$> extractTvbKind_maybe sig_tvb

          mb_kind :: Maybe Kind
          mb_kind =
            case (mb_decl_bndr_kind, mb_sig_tvb_kind) of
              (Nothing,             Nothing)           -> Nothing
              (Just decl_bndr_kind, Nothing)           -> Just decl_bndr_kind
              (Nothing,             Just sig_tvb_kind) -> Just sig_tvb_kind
              (Just decl_bndr_kind, Just sig_tvb_kind) -> do
                match_subst <- matchTy decl_bndr_kind sig_tvb_kind
                Just $ applySubstitution match_subst decl_bndr_kind

          subst' = Map.insert sig_tvb_name (VarT decl_bndr_name) subst
          sig_tvb' = case mb_kind of
            Nothing   -> plainTVFlag decl_bndr_name sig_tvb_flag
            Just kind -> kindedTVFlag decl_bndr_name sig_tvb_flag kind in

      (subst', sig_tvb')

-- Collect the invisible type variable binders from a sequence of FunArgs.
filterInvisTvbArgs :: FunArgs -> [TyVarBndrSpec]
filterInvisTvbArgs FANil           = []
filterInvisTvbArgs (FACxt  _ args) = filterInvisTvbArgs args
filterInvisTvbArgs (FAAnon _ args) = filterInvisTvbArgs args
filterInvisTvbArgs (FAForalls tele args) =
  let res = filterInvisTvbArgs args in
  case tele of
    ForallVis   _     -> res
    ForallInvis tvbs' -> tvbs' ++ res

-- | Take a telescope of 'TyVarBndr's, find the free variables in their kinds,
-- and sort them in reverse topological order to ensure that they are well
-- scoped. Because the argument list is assumed to be telescoping, kind
-- variables that are bound earlier in the list are not returned. For example,
-- this:
--
-- @
-- 'freeKindVariablesWellScoped' [a :: k, b :: Proxy a]
-- @
--
-- Will return @[k]@, not @[k, a]@, since @a@ is bound earlier by @a :: k@.
freeKindVariablesWellScoped :: [TyVarBndr_ flag] -> [TyVarBndrUnit]
freeKindVariablesWellScoped tvbs =
  foldr (\tvb kvs ->
          foldMap (\t -> freeVariablesWellScoped [t]) (extractTvbKind_maybe tvb) `List.union`
          List.deleteBy ((==) `on` tvName) tvb kvs)
        []
        (changeTVFlags () tvbs)

-- | @'matchTy' tmpl targ@ matches a type template @tmpl@ against a type target
-- @targ@. This returns a Map from names of type variables in the type template
-- to types if the types indeed match up, or @Nothing@ otherwise. In the @Just@
-- case, it is guaranteed that every type variable mentioned in the template is
-- mapped by the returned substitution.
--
-- Note that this function will always return @Nothing@ if the template contains
-- an explicit kind signature or visible kind application.
--
-- This is heavily inspired by the function of the same name in
-- "Language.Haskell.TH.Desugar.Subst", which works over 'DType's instead of
-- 'Type's.
matchTy :: Type -> Type -> Maybe (Map Name Type)
matchTy (VarT var_name) arg = Just $ Map.singleton var_name arg
matchTy (SigT {})     _ = Nothing
matchTy pat (SigT     ty _ki) = matchTy pat ty
#if __GLASGOW_HASKELL__ >= 807
matchTy (AppKindT {}) _ = Nothing
matchTy pat (AppKindT ty _ki) = matchTy pat ty
#endif
matchTy (ForallT {}) _ =
  error "Cannot match a forall in a pattern"
matchTy _ (ForallT {}) =
  error "Cannot match a forall in a target"
matchTy (AppT pat1 pat2) (AppT arg1 arg2) =
  unionMaybeSubsts [matchTy pat1 arg1, matchTy pat2 arg2]
matchTy (ConT pat_con) (ConT arg_con)
  | pat_con == arg_con
  = Just Map.empty
  | otherwise
  = Nothing
matchTy ArrowT ArrowT = Just Map.empty
matchTy (LitT pat_lit) (LitT arg_lit)
  | pat_lit == arg_lit
  = Just Map.empty
  | otherwise
  = Nothing
matchTy _ _ = Nothing

-- | This is inspired by the function of the same name in
-- "Language.Haskell.TH.Desugar.Subst".
unionMaybeSubsts :: [Maybe (Map Name Type)] -> Maybe (Map Name Type)
unionMaybeSubsts = List.foldl' union_subst1 (Just Map.empty)
  where
    union_subst1 ::
      Maybe (Map Name Type) -> Maybe (Map Name Type) -> Maybe (Map Name Type)
    union_subst1 ma mb = do
      a <- ma
      b <- mb
      unionSubsts a b

-- | Computes the union of two substitutions. Fails if both subsitutions map
-- the same variable to different types.
--
-- This is inspired by the function of the same name in
-- "Language.Haskell.TH.Desugar.Subst".
unionSubsts :: Map Name Type -> Map Name Type -> Maybe (Map Name Type)
unionSubsts a b =
  let shared_key_set = Map.keysSet a `Set.intersection` Map.keysSet b
      matches_up     = Set.foldr (\name -> ((a Map.! name) == (b Map.! name) &&))
                                 True shared_key_set
  in
  if matches_up then return (a `Map.union` b) else Nothing

-- | This is inspired by the function of the same name in
-- "Language.Haskell.TH.Desugar.Subst.Capturing".
substTvb :: Map Name Kind -> TyVarBndr_ flag -> (Map Name Kind, TyVarBndr_ flag)
substTvb s tvb = (Map.delete (tvName tvb) s, mapTVKind (applySubstitution s) tvb)

-- This is heavily inspired by the `swizzleTcb` function in GHC:
-- https://gitlab.haskell.org/ghc/ghc/-/blob/cec903899234bf9e25ea404477ba846ac1e963bb/compiler/GHC/Tc/Gen/HsType.hs#L2741-2755
swizzleTvb ::
     Map Name Name
     -- ^ A \"swizzle environment\" (i.e., a map from binder names in a
     -- standalone kind signature to binder names in the corresponding
     -- type-level declaration).
  -> Map Name Type
     -- ^ Like the swizzle environment, but as a full-blown substitution.
  -> TyVarBndr_ flag
  -> (Map Name Type, TyVarBndr_ flag)
swizzleTvb swizzle_env subst tvb =
  (subst', tvb2)
  where
    subst' = Map.insert tvb_name (VarT (tvName tvb2)) subst
    tvb_name = tvName tvb
    tvb1 = mapTVKind (applySubstitution subst) tvb
    tvb2 =
      case Map.lookup tvb_name swizzle_env of
        Just user_name -> mapTVName (const user_name) tvb1
        Nothing        -> tvb1

-- The visibility of a binder in a type-level declaration. This generalizes
-- 'Specificity' (which lacks an equivalent to 'Required') and 'BndrVis' (which
-- lacks an equivalent to @'Invisible' 'Inferred'@).
--
-- This is heavily inspired by a data type of the same name in GHC:
-- https://gitlab.haskell.org/ghc/ghc/-/blob/98597ad5fca81544d74f721fb508295fd2650232/compiler/GHC/Types/Var.hs#L458-465
data ForAllTyFlag
  = Invisible !Specificity
    -- ^ If the 'Specificity' value is 'SpecifiedSpec', then the binder is
    -- permitted by request (e.g., @\@a@). If the 'Specificity' value is
    -- 'InferredSpec', then the binder is prohibited from appearing in source
    -- Haskell (e.g., @\@{a}@).
  | Required
    -- ^ The binder is required to appear in source Haskell (e.g., @a@).
  deriving (Show, Eq, Ord, Data, Generic, Lift)

instance DefaultBndrFlag ForAllTyFlag where
  defaultBndrFlag = Required

#if __GLASGOW_HASKELL__ >= 900
instance PprFlag ForAllTyFlag where
  pprTyVarBndr (PlainTV nm vis) =
    pprForAllTyFlag vis (ppr nm)
  pprTyVarBndr (KindedTV nm vis k) =
    pprForAllTyFlag vis (Ppr.parens (ppr nm Ppr.<+> Ppr.dcolon Ppr.<+> ppr k))

pprForAllTyFlag :: ForAllTyFlag -> Ppr.Doc -> Ppr.Doc
pprForAllTyFlag (Invisible SpecifiedSpec) d = Ppr.char '@' Ppr.<> d
pprForAllTyFlag (Invisible InferredSpec)  d = Ppr.braces d
pprForAllTyFlag Required                  d = d
#endif

-- | Convert a list of @'TyVarBndr' 'ForAllTyFlag'@s to a list of
-- 'TyVarBndrSpec's, which is suitable for use in an invisible @forall@.
-- Specifically:
--
-- * Variable binders that use @'Invisible' spec@ are converted to @spec@.
--
-- * Variable binders that are 'Required' are converted to 'SpecifiedSpec',
--   as all of the 'TyVarBndrSpec's are invisible. As an example of how this
--   is used, consider what would happen when singling this data type:
--
--   @
--   type T :: forall k -> k -> Type
--   data T k (a :: k) where ...
--   @
--
--   Here, the @k@ binder is 'Required'. When we produce the standalone kind
--   signature for the singled data type, we use 'tvbForAllTyFlagsToSpecs' to
--   produce the type variable binders in the outermost @forall@:
--
--   @
--   type ST :: forall k (a :: k). T k a -> Type
--   data ST z where ...
--   @
--
--   Note that the @k@ is bound visibily (i.e., using 'SpecifiedSpec') in the
--   outermost, invisible @forall@.
tvbForAllTyFlagsToSpecs :: [TyVarBndr_ ForAllTyFlag] -> [TyVarBndrSpec]
tvbForAllTyFlagsToSpecs = map (mapTVFlag to_spec)
  where
   to_spec :: ForAllTyFlag -> Specificity
   to_spec (Invisible spec) = spec
   to_spec Required         = SpecifiedSpec

-- | Convert a list of @'TyVarBndr' 'ForAllTyFlag'@s to a list of
-- 'TyVarBndrVis'es, which is suitable for use in a type-level declaration
-- (e.g., the @var_1 ... var_n@ in @class C var_1 ... var_n@). Specifically:
--
-- * Variable binders that use @'Invisible' 'InferredSpec'@ are dropped
--   entirely. Such binders cannot be represented in source Haskell.
--
-- * Variable binders that use @'Invisible' 'SpecifiedSpec'@ are converted to
--   'BndrInvis'.
--
-- * Variable binders that are 'Required' are converted to 'BndrReq'.
tvbForAllTyFlagsToBndrVis :: [TyVarBndr_ ForAllTyFlag] -> [TyVarBndrVis]
tvbForAllTyFlagsToBndrVis = catMaybes . map (traverseTVFlag to_spec_maybe)
  where
    to_spec_maybe :: ForAllTyFlag -> Maybe BndrVis
    to_spec_maybe (Invisible InferredSpec) = Nothing
    to_spec_maybe (Invisible SpecifiedSpec) = Just bndrInvis
    to_spec_maybe Required = Just BndrReq

----------------------------------------
-- Free names, etc.
----------------------------------------

-- | Check if a name occurs anywhere within a TH tree.
nameOccursIn :: Data a => Name -> a -> Bool
nameOccursIn n = everything (||) $ mkQ False (== n)

-- | Extract all Names mentioned in a TH tree.
allNamesIn :: Data a => a -> [Name]
allNamesIn = everything (++) $ mkQ [] (:[])

-- | Extract the names bound in a @Stmt@.
--
-- This does /not/ extract any type variables bound by pattern signatures,
-- constructor patterns, or type patterns.
extractBoundNamesStmt :: Stmt -> OSet Name
extractBoundNamesStmt (BindS pat _) = extractBoundNamesPat pat
extractBoundNamesStmt (LetS decs)   = foldMap extractBoundNamesDec decs
extractBoundNamesStmt (NoBindS _)   = OS.empty
extractBoundNamesStmt (ParS stmtss) = foldMap (foldMap extractBoundNamesStmt) stmtss
#if __GLASGOW_HASKELL__ >= 807
extractBoundNamesStmt (RecS stmtss) = foldMap extractBoundNamesStmt stmtss
#endif

-- | Extract the names bound in a @Dec@ that could appear in a @let@ expression.
--
-- This does /not/ extract any type variables bound by pattern signatures,
-- constructor patterns, or type patterns.
extractBoundNamesDec :: Dec -> OSet Name
extractBoundNamesDec (FunD name _)  = OS.singleton name
extractBoundNamesDec (ValD pat _ _) = extractBoundNamesPat pat
extractBoundNamesDec _              = OS.empty

-- | Extract the names bound in a @Pat@.
--
-- This does /not/ extract any type variables bound by pattern signatures,
-- constructor patterns, or type patterns.
extractBoundNamesPat :: Pat -> OSet Name
extractBoundNamesPat (LitP _)              = OS.empty
extractBoundNamesPat (VarP name)           = OS.singleton name
extractBoundNamesPat (TupP pats)           = foldMap extractBoundNamesPat pats
extractBoundNamesPat (UnboxedTupP pats)    = foldMap extractBoundNamesPat pats
extractBoundNamesPat (ConP _
#if __GLASGOW_HASKELL__ >= 901
                             _
#endif
                               pats)       = foldMap extractBoundNamesPat pats
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
#if __GLASGOW_HASKELL__ >= 909
extractBoundNamesPat (TypeP _)             = OS.empty
extractBoundNamesPat (InvisP _)            = OS.empty
#endif
#if __GLASGOW_HASKELL__ >= 911
extractBoundNamesPat (OrP pats)            = foldMap extractBoundNamesPat pats
#endif

----------------------------------------
-- General utility
----------------------------------------

-- dirty implementation of explicit-to-implicit conversion
newtype MagicIP name a r = MagicIP (IP name a => r)

-- | Get an implicit param constraint (@IP name a@, which is the desugared
-- form of @(?name :: a)@) from an explicit value.
--
-- This function is only available with GHC 8.0 or later.
bindIP :: forall name a r. a -> (IP name a => r) -> r
bindIP val k = (unsafeCoerce (MagicIP @name k) :: a -> r) val

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

firstMatchM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstMatchM f xs = listToMaybe <$> mapMaybeM f xs

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

-- | The 'Name' of the kind 'Kind.Type'.
-- 2. The kind @*@ on older GHCs.
typeKindName :: Name
typeKindName = ''Kind.Type

#if __GLASGOW_HASKELL__ < 805
-- | The 'Name' of the kind @*@.
starKindName :: Name
starKindName = ''(Kind.*)

-- | The 'Name' of the kind 'Kind.★'.
uniStarKindName :: Name
uniStarKindName = ''(Kind.★)
#endif

-- | Is a data type or data instance declaration a @newtype@ declaration, a
-- @data@ declaration, or a @type data@ declaration?
data DataFlavor
  = Newtype  -- ^ @newtype@
  | Data     -- ^ @data@
  | TypeData -- ^ @type data@
  deriving (Eq, Show, Data, Generic, Lift)
