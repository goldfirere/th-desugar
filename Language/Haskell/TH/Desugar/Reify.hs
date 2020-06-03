{- Language/Haskell/TH/Desugar/Reify.hs

(c) Richard Eisenberg 2014
rae@cs.brynmawr.edu

Allows for reification from a list of declarations, without looking a name
up in the environment.
-}

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, ScopedTypeVariables #-}

module Language.Haskell.TH.Desugar.Reify (
  -- * Reification
  reifyWithLocals_maybe, reifyWithLocals, reifyWithWarning, reifyInDecs,

  -- ** Fixity reification
  qReifyFixity, reifyFixity, reifyFixityWithLocals, reifyFixityInDecs,

  -- ** Type reification
  qReifyType, reifyType,
  reifyTypeWithLocals_maybe, reifyTypeWithLocals, reifyTypeInDecs,

  -- * Datatype lookup
  getDataD, dataConNameToCon, dataConNameToDataName,

  -- * Value and type lookup
  lookupValueNameWithLocals, lookupTypeNameWithLocals,
  mkDataNameWithLocals, mkTypeNameWithLocals,
  reifyNameSpace,

  -- * Monad support
  DsMonad(..), DsM, withLocalDeclarations
  ) where

import Control.Applicative
import qualified Control.Monad.Fail as Fail
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Trans.Instances ()
import qualified Data.Foldable as F
#if __GLASGOW_HASKELL__ < 710
import Data.Foldable (foldMap)
#endif
import Data.Function (on)
import Data.List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)

import Language.Haskell.TH.Datatype
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax hiding ( lift )

import Language.Haskell.TH.Desugar.Util

-- | Like @reify@ from Template Haskell, but looks also in any not-yet-typechecked
-- declarations. To establish this list of not-yet-typechecked declarations,
-- use 'withLocalDeclarations'. Returns 'Nothing' if reification fails.
-- Note that no inferred type information is available from local declarations;
-- bottoms may be used if necessary.
reifyWithLocals_maybe :: DsMonad q => Name -> q (Maybe Info)
reifyWithLocals_maybe name = qRecover
  (return . reifyInDecs name =<< localDeclarations)
  (Just `fmap` qReify name)

-- | Like 'reifyWithLocals_maybe', but throws an exception upon failure,
-- warning the user about separating splices.
reifyWithLocals :: DsMonad q => Name -> q Info
reifyWithLocals name = do
  m_info <- reifyWithLocals_maybe name
  case m_info of
    Nothing -> reifyFail name
    Just i  -> return i

-- | Reify a declaration, warning the user about splices if the reify fails.
-- The warning says that reification can fail if you try to reify a type in
-- the same splice as it is declared.
reifyWithWarning :: (Quasi q, Fail.MonadFail q) => Name -> q Info
reifyWithWarning name = qRecover (reifyFail name) (qReify name)

-- | Print out a warning about separating splices and fail.
reifyFail :: Fail.MonadFail m => Name -> m a
reifyFail name =
  Fail.fail $ "Looking up " ++ (show name) ++ " in the list of available " ++
              "declarations failed.\nThis lookup fails if the declaration " ++
              "referenced was made in the same Template\nHaskell splice as the use " ++
              "of the declaration. If this is the case, put\nthe reference to " ++
              "the declaration in a new splice."

---------------------------------
-- Utilities
---------------------------------

-- | Extract the @TyVarBndr@s and constructors given the @Name@ of a type
getDataD :: DsMonad q
         => String       -- ^ Print this out on failure
         -> Name         -- ^ Name of the datatype (@data@ or @newtype@) of interest
         -> q ([TyVarBndrUnit], [Con])
getDataD err name = do
  info <- reifyWithLocals name
  dec <- case info of
           TyConI dec -> return dec
           _ -> badDeclaration
  case dec of
#if __GLASGOW_HASKELL__ > 710
    DataD _cxt _name tvbs mk cons _derivings -> go tvbs mk cons
    NewtypeD _cxt _name tvbs mk con _derivings -> go tvbs mk [con]
#else
    DataD _cxt _name tvbs cons _derivings -> go tvbs Nothing cons
    NewtypeD _cxt _name tvbs con _derivings -> go tvbs Nothing [con]
#endif
    _ -> badDeclaration
  where
    go tvbs mk cons = do
      let k = fromMaybe (ConT typeKindName) mk
      extra_tvbs <- mkExtraKindBinders k
      let all_tvbs = tvbs ++ extra_tvbs
      return (all_tvbs, cons)

    badDeclaration =
          fail $ "The name (" ++ (show name) ++ ") refers to something " ++
                 "other than a datatype. " ++ err

-- | Create new kind variable binder names corresponding to the return kind of
-- a data type. This is useful when you have a data type like:
--
-- @
-- data Foo :: forall k. k -> Type -> Type where ...
-- @
--
-- But you want to be able to refer to the type @Foo a b@.
-- 'mkExtraKindBinders' will take the kind @forall k. k -> Type -> Type@,
-- discover that is has two visible argument kinds, and return as a result
-- two new kind variable binders @[a :: k, b :: Type]@, where @a@ and @b@
-- are fresh type variable names.
--
-- This expands kind synonyms if necessary.
mkExtraKindBinders :: forall q. Quasi q => Kind -> q [TyVarBndrUnit]
mkExtraKindBinders k = do
  k' <- runQ $ resolveTypeSynonyms k
  let (fun_args, _) = unravelType k'
      vis_fun_args  = filterVisFunArgs fun_args
  mapM mk_tvb vis_fun_args
  where
    mk_tvb :: VisFunArg -> q TyVarBndrUnit
    mk_tvb (VisFADep tvb) = return tvb
    mk_tvb (VisFAAnon ki) = kindedTV <$> qNewName "a" <*> return ki

-- | From the name of a data constructor, retrive the datatype definition it
-- is a part of.
dataConNameToDataName :: DsMonad q => Name -> q Name
dataConNameToDataName con_name = do
  info <- reifyWithLocals con_name
  case info of
#if __GLASGOW_HASKELL__ > 710
    DataConI _name _type parent_name -> return parent_name
#else
    DataConI _name _type parent_name _fixity -> return parent_name
#endif
    _ -> fail $ "The name " ++ show con_name ++ " does not appear to be " ++
                "a data constructor."

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: DsMonad q => Name -> q Con
dataConNameToCon con_name = do
  -- we need to get the field ordering from the constructor. We must reify
  -- the constructor to get the tycon, and then reify the tycon to get the `Con`s
  type_name <- dataConNameToDataName con_name
  (_, cons) <- getDataD "This seems to be an error in GHC." type_name
  let m_con = find (any (con_name ==) . get_con_name) cons
  case m_con of
    Just con -> return con
    Nothing -> impossible "Datatype does not contain one of its own constructors."

  where
    get_con_name (NormalC name _)     = [name]
    get_con_name (RecC name _)        = [name]
    get_con_name (InfixC _ name _)    = [name]
    get_con_name (ForallC _ _ con)    = get_con_name con
#if __GLASGOW_HASKELL__ > 710
    get_con_name (GadtC names _ _)    = names
    get_con_name (RecGadtC names _ _) = names
#endif

--------------------------------------------------
-- DsMonad
--------------------------------------------------

-- | A 'DsMonad' stores some list of declarations that should be considered
-- in scope. 'DsM' is the prototypical inhabitant of 'DsMonad'.
class (Quasi m, Fail.MonadFail m) => DsMonad m where
  -- | Produce a list of local declarations.
  localDeclarations :: m [Dec]

instance DsMonad Q where
  localDeclarations = return []
instance DsMonad IO where
  localDeclarations = return []

-- | A convenient implementation of the 'DsMonad' class. Use by calling
-- 'withLocalDeclarations'.
newtype DsM q a = DsM (ReaderT [Dec] q a)
  deriving ( Functor, Applicative, Monad, MonadTrans, Quasi, Fail.MonadFail
#if __GLASGOW_HASKELL__ >= 803
           , MonadIO
#endif
           )

instance (Quasi q, Fail.MonadFail q) => DsMonad (DsM q) where
  localDeclarations = DsM ask

instance DsMonad m => DsMonad (ReaderT r m) where
  localDeclarations = lift localDeclarations

instance DsMonad m => DsMonad (StateT s m) where
  localDeclarations = lift localDeclarations

instance (DsMonad m, Monoid w) => DsMonad (WriterT w m) where
  localDeclarations = lift localDeclarations

instance (DsMonad m, Monoid w) => DsMonad (RWST r w s m) where
  localDeclarations = lift localDeclarations

-- | Add a list of declarations to be considered when reifying local
-- declarations.
withLocalDeclarations :: DsMonad q => [Dec] -> DsM q a -> q a
withLocalDeclarations new_decs (DsM x) = do
  orig_decs <- localDeclarations
  runReaderT x (orig_decs ++ new_decs)

---------------------------
-- Reifying local declarations
---------------------------

-- | Look through a list of declarations and possibly return a relevant 'Info'
reifyInDecs :: Name -> [Dec] -> Maybe Info
reifyInDecs n decs = snd `fmap` firstMatch (reifyInDec n decs) decs

-- | Look through a list of declarations and possibly return a fixity.
reifyFixityInDecs :: Name -> [Dec] -> Maybe Fixity
reifyFixityInDecs n = firstMatch match_fixity
  where
    match_fixity (InfixD fixity n')        | n `nameMatches` n'
                                           = Just fixity
    match_fixity (ClassD _ _ _ _ sub_decs) = firstMatch match_fixity sub_decs
    match_fixity _                         = Nothing

-- | A reified thing along with the name of that thing.
type Named a = (Name, a)

reifyInDec :: Name -> [Dec] -> Dec -> Maybe (Named Info)
reifyInDec n decs (FunD n' _) | n `nameMatches` n' = Just (n', mkVarI n decs)
reifyInDec n decs (ValD pat _ _)
  | Just n' <- find (nameMatches n) (F.toList (extractBoundNamesPat pat)) = Just (n', mkVarI n decs)
#if __GLASGOW_HASKELL__ > 710
reifyInDec n _    dec@(DataD    _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(NewtypeD _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
#else
reifyInDec n _    dec@(DataD    _ n' _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(NewtypeD _ n' _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
#endif
reifyInDec n _    dec@(TySynD n' _ _)       | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n decs dec@(ClassD _ n' _ _ _)   | n `nameMatches` n'
  = Just (n', ClassI (quantifyClassDecMethods dec) (findInstances n decs))
reifyInDec n decs (ForeignD (ImportF _ _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n decs ty)
reifyInDec n decs (ForeignD (ExportF _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n decs ty)
#if __GLASGOW_HASKELL__ > 710
reifyInDec n decs dec@(OpenTypeFamilyD (TypeFamilyHead n' _ _ _)) | n `nameMatches` n'
  = Just (n', FamilyI dec (findInstances n decs))
reifyInDec n decs dec@(DataFamilyD n' _ _) | n `nameMatches` n'
  = Just (n', FamilyI dec (findInstances n decs))
reifyInDec n _    dec@(ClosedTypeFamilyD (TypeFamilyHead n' _ _ _) _) | n `nameMatches` n'
  = Just (n', FamilyI dec [])
#else
reifyInDec n decs dec@(FamilyD _ n' _ _) | n `nameMatches` n'
  = Just (n', FamilyI dec (findInstances n decs))
reifyInDec n _    dec@(ClosedTypeFamilyD n' _ _ _) | n `nameMatches` n'
  = Just (n', FamilyI dec [])
#endif
#if __GLASGOW_HASKELL__ >= 801
reifyInDec n decs (PatSynD n' _ _ _) | n `nameMatches` n'
  = Just (n', mkPatSynI n decs)
#endif

#if __GLASGOW_HASKELL__ > 710
reifyInDec n decs (DataD _ ty_name tvbs _mk cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs _mk con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) [con]
  = Just info
#else
reifyInDec n decs (DataD _ ty_name tvbs cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) [con]
  = Just info
#endif
#if __GLASGOW_HASKELL__ > 710
reifyInDec n _decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just (n', ty) <- findType n sub_decs
  = Just (n', ClassOpI n (quantifyClassMethodType ty_name tvbs True ty) ty_name)
#else
reifyInDec n decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just (n', ty) <- findType n sub_decs
  = Just (n', ClassOpI n (quantifyClassMethodType ty_name tvbs True ty)
                       ty_name (fromMaybe defaultFixity $
                                reifyFixityInDecs n $ sub_decs ++ decs))
#endif
reifyInDec n decs (ClassD _ _ _ _ sub_decs)
  | Just info <- firstMatch (reifyInDec n decs) sub_decs
                 -- Important: don't pass (sub_decs ++ decs) to reifyInDec
                 -- above, or else type family defaults can be confused for
                 -- actual instances. See #134.
  = Just info
#if __GLASGOW_HASKELL__ >= 711
reifyInDec n decs (InstanceD _ _ _ sub_decs)
#else
reifyInDec n decs (InstanceD _ _ sub_decs)
#endif
  | Just info <- firstMatch reify_in_instance sub_decs
  = Just info
  where
    reify_in_instance dec@(DataInstD {})    = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance dec@(NewtypeInstD {}) = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance _                     = Nothing
#if __GLASGOW_HASKELL__ >= 807
reifyInDec n decs (DataInstD _ _ lhs _ cons _)
  | (ConT ty_name, tys) <- unfoldType lhs
  , Just info <- maybeReifyCon n decs ty_name tys cons
  = Just info
reifyInDec n decs (NewtypeInstD _ _ lhs _ con _)
  | (ConT ty_name, tys) <- unfoldType lhs
  , Just info <- maybeReifyCon n decs ty_name tys [con]
  = Just info
#elif __GLASGOW_HASKELL__ > 710
reifyInDec n decs (DataInstD _ ty_name tys _ cons _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys _ con _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) [con]
  = Just info
#else
reifyInDec n decs (DataInstD _ ty_name tys cons _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys con _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) [con]
  = Just info
#endif

reifyInDec _ _ _ = Nothing

maybeReifyCon :: Name -> [Dec] -> Name -> [TypeArg] -> [Con] -> Maybe (Named Info)
maybeReifyCon n _decs ty_name ty_args cons
  | Just (n', con) <- findCon n cons
    -- See Note [Use unSigType in maybeReifyCon]
  , let full_con_ty = unSigType $ con_to_type h98_tvbs h98_res_ty con
  = Just ( n', DataConI n full_con_ty ty_name
#if __GLASGOW_HASKELL__ < 800
                        fixity
#endif
         )

  | Just (n', rec_sel_info) <- findRecSelector n cons
  , let (tvbs, sel_ty, con_res_ty) = extract_rec_sel_info rec_sel_info
        -- See Note [Use unSigType in maybeReifyCon]
        full_sel_ty = unSigType $ maybeForallT tvbs [] $ mkArrows [con_res_ty] sel_ty
      -- we don't try to ferret out naughty record selectors.
  = Just ( n', VarI n full_sel_ty Nothing
#if __GLASGOW_HASKELL__ < 800
                    fixity
#endif
         )
  where
    extract_rec_sel_info :: RecSelInfo -> ([TyVarBndrUnit], Type, Type)
      -- Returns ( Selector type variable binders
      --         , Record field type
      --         , constructor result type )
    extract_rec_sel_info rec_sel_info =
      case rec_sel_info of
        RecSelH98 sel_ty -> (h98_tvbs, sel_ty, h98_res_ty)
        RecSelGADT sel_ty con_res_ty ->
          ( freeVariablesWellScoped [con_res_ty, sel_ty]
          , sel_ty, con_res_ty)

    h98_tvbs   = freeVariablesWellScoped $ map probablyWrongUnTypeArg ty_args
    h98_res_ty = applyType (ConT ty_name) ty_args

#if __GLASGOW_HASKELL__ < 800
    fixity = fromMaybe defaultFixity $ reifyFixityInDecs n _decs
#endif
maybeReifyCon _ _ _ _ _ = Nothing

{-
Note [Use unSigType in maybeReifyCon]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Make sure to call unSigType on the type of a reified data constructor or
record selector. Otherwise, if you have this:

  data D (a :: k) = MkD { unD :: Proxy a }

Then the type of unD will be reified as:

  unD :: forall k (a :: k). D (a :: k) -> Proxy a

This is contrast to GHC's own reification, which will produce `D a`
(without the explicit kind signature) as the type of the first argument.
-}

-- Reverse-engineer the type of a data constructor.
con_to_type :: [TyVarBndrUnit] -- The type variables bound by a data type head.
                               -- Only used for Haskell98-style constructors.
            -> Type            -- The constructor result type.
                               -- Only used for Haskell98-style constructors.
            -> Con -> Type
con_to_type h98_tvbs h98_result_ty con =
  case go con of
    (is_gadt, ty) | is_gadt   -> ty
                  | otherwise -> maybeForallT h98_tvbs [] ty
  where
    go :: Con -> (Bool, Type) -- The Bool is True when dealing with a GADT
    go (NormalC _ stys)       = (False, mkArrows (map snd    stys)  h98_result_ty)
    go (RecC _ vstys)         = (False, mkArrows (map thdOf3 vstys) h98_result_ty)
    go (InfixC t1 _ t2)       = (False, mkArrows (map snd [t1, t2]) h98_result_ty)
    go (ForallC bndrs cxt c)  = liftSnd (ForallT bndrs cxt) (go c)
#if __GLASGOW_HASKELL__ > 710
    go (GadtC _ stys rty)     = (True, mkArrows (map snd    stys)  rty)
    go (RecGadtC _ vstys rty) = (True, mkArrows (map thdOf3 vstys) rty)
#endif

mkVarI :: Name -> [Dec] -> Info
mkVarI n decs = mkVarITy n decs (maybe (no_type n) snd $ findType n decs)

mkVarITy :: Name -> [Dec] -> Type -> Info
#if __GLASGOW_HASKELL__ > 710
mkVarITy n _decs ty = VarI n ty Nothing
#else
mkVarITy n decs ty = VarI n ty Nothing (fromMaybe defaultFixity $
                                        reifyFixityInDecs n decs)
#endif

findType :: Name -> [Dec] -> Maybe (Named Type)
findType n = firstMatch match_type
  where
    match_type (SigD n' ty) | n `nameMatches` n' = Just (n', ty)
    match_type _                                 = Nothing

#if __GLASGOW_HASKELL__ >= 801
mkPatSynI :: Name -> [Dec] -> Info
mkPatSynI n decs = PatSynI n (fromMaybe (no_type n) $ findPatSynType n decs)

findPatSynType :: Name -> [Dec] -> Maybe PatSynType
findPatSynType n = firstMatch match_pat_syn_type
  where
    match_pat_syn_type (PatSynSigD n' psty) | n `nameMatches` n' = Just psty
    match_pat_syn_type _                                         = Nothing
#endif

no_type :: Name -> Type
no_type n = error $ "No type information found in local declaration for "
                    ++ show n

findInstances :: Name -> [Dec] -> [Dec]
findInstances n = map stripInstanceDec . concatMap match_instance
  where
#if __GLASGOW_HASKELL__ >= 711
    match_instance d@(InstanceD _ _ ty _)
#else
    match_instance d@(InstanceD _ ty _)
#endif
                                               | ConT n' <- ty_head ty
                                               , n `nameMatches` n' = [d]
#if __GLASGOW_HASKELL__ >= 807
    match_instance (DataInstD ctxt _ lhs mk cons derivs)
                                                  | ConT n' <- ty_head lhs
                                                  , n `nameMatches` n' = [d]
      where
        mtvbs = rejig_data_inst_tvbs ctxt lhs mk
        d = DataInstD ctxt mtvbs lhs mk cons derivs
    match_instance (NewtypeInstD ctxt _ lhs mk con derivs)
                                                  | ConT n' <- ty_head lhs
                                                  , n `nameMatches` n' = [d]
      where
        mtvbs = rejig_data_inst_tvbs ctxt lhs mk
        d = NewtypeInstD ctxt mtvbs lhs mk con derivs
#elif __GLASGOW_HASKELL__ > 710
    match_instance d@(DataInstD _ n' _ _ _ _)    | n `nameMatches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _ _) | n `nameMatches` n' = [d]
#else
    match_instance d@(DataInstD _ n' _ _ _)    | n `nameMatches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _) | n `nameMatches` n' = [d]
#endif
#if __GLASGOW_HASKELL__ >= 807
    match_instance (TySynInstD (TySynEqn _ lhs rhs))
                                               | ConT n' <- ty_head lhs
                                               , n `nameMatches` n' = [d]
      where
        mtvbs = rejig_tvbs [lhs, rhs]
        d = TySynInstD (TySynEqn mtvbs lhs rhs)
#else
    match_instance d@(TySynInstD n' _)         | n `nameMatches` n' = [d]
#endif

#if __GLASGOW_HASKELL__ >= 711
    match_instance (InstanceD _ _ _ decs)
#else
    match_instance (InstanceD _ _ decs)
#endif
                                        = concatMap match_instance decs
    match_instance _                    = []

#if __GLASGOW_HASKELL__ >= 807
    -- See Note [Rejigging reified type family equations variable binders]
    -- for why this is necessary.
    rejig_tvbs :: [Type] -> Maybe [TyVarBndrUnit]
    rejig_tvbs ts =
      let tvbs = freeVariablesWellScoped ts
      in if null tvbs
         then Nothing
         else Just tvbs

    rejig_data_inst_tvbs :: Cxt -> Type -> Maybe Kind -> Maybe [TyVarBndrUnit]
    rejig_data_inst_tvbs cxt lhs mk =
      rejig_tvbs $ cxt ++ [lhs] ++ maybeToList mk
#endif

    ty_head = fst . unfoldType

{-
Note [Rejigging reified type family equations variable binders]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
When reifying a type family instance (on GHC 8.8 or later), which quantified
type variables do you use? This might seem like a strange question to ask since
these instances already come equipped with a field of type `Maybe [TyVarBndr]`,
but it's not always the case that you want to use exactly that field. Here is
an example to better explain it:

  class C a where
    type T b a
  instance C (Maybe a) where
    type forall b. T b (Maybe a) = a

If the above instance were quoted, it would give you `Just [PlainTV b]`. But if
you were to reify ''T (and therefore retrieve the instance for T), you wouldn't
want to use that as your list of type variable binders! This is because
reifiying any type family always presents the information as though the type
family were top-level. Therefore, reifying T (in GHC, at least) would yield:

  type family T b a
  type instance forall b a. T b (Maybe a) = a

Note that we quantify over `b` *and* `a` here, not just `b`. To emulate this
GHC quirk, whenever we reify any type family instance, we just ignore the field
of type `Maybe [TyVarBndr]` and quantify over the instance afresh. It's a bit
tedious, but it gets the job done. (This is accomplished by the rejig_tvbs
function.)
-}

-- Consider the following class declaration:
--
--   [d| class C a where
--         method :: a -> b -> a |]
--
-- When reifying C locally, quantifyClassDecMethods serves two purposes:
--
-- 1. It quantifies the class method's local type variables. To illustrate this
--    point, this is how GHC would reify C:
--
--      class C a where
--        method :: forall b. a -> b -> a
--
--    Notice the presence of the explicit `forall b.`. quantifyClassDecMethods
--    performs this explicit quantification if necessary (as in the case in the
--    local C declaration, where `b` is implicitly quantified.)
-- 2. It emulates a quirk in the way old versions of GHC would reify class
--    declarations (Trac #15551). On versions of GHC older than 8.8, it would
--    reify C like so:
--
--      class C a where
--        method :: forall a. C a => forall b. a -> b -> a
--
--    Notice how GHC has added the (totally extraneous) `forall a. C a =>`
--    part! This is weird, but our primary goal in this module is to mimic
--    GHC's reification, so we play the part by adding the `forall`/class
--    context to each class method in quantifyClassDecMethods.
--
--    Since Trac #15551 was fixed in GHC 8.8, this function doesn't perform
--    this step on 8.7 or later.
quantifyClassDecMethods :: Dec -> Dec
quantifyClassDecMethods (ClassD cxt cls_name cls_tvbs fds sub_decs)
  = ClassD cxt cls_name cls_tvbs fds sub_decs'
  where
    sub_decs' = mapMaybe go sub_decs
    go (SigD n ty) =
      Just $ SigD n
           $ quantifyClassMethodType cls_name cls_tvbs prepend_cls ty
    go d@(TySynInstD {})      = Just d
#if __GLASGOW_HASKELL__ > 710
    go d@(OpenTypeFamilyD {}) = Just d
    go d@(DataFamilyD {})     = Just d
#endif
    go _           = Nothing

    -- See (2) in the comments for quantifyClassDecMethods.
    prepend_cls :: Bool
#if __GLASGOW_HASKELL__ >= 807
    prepend_cls = False
#else
    prepend_cls = True
#endif
quantifyClassDecMethods dec = dec

-- Add explicit quantification to a class method's type if necessary. In this
-- example:
--
--   [d| class C a where
--         method :: a -> b -> a |]
--
-- If one invokes `quantifyClassMethodType C [a] prepend (a -> b -> a)`, then
-- the output will be:
--
-- 1. `forall a. C a => forall b. a -> b -> a` (if `prepend` is True)
-- 2.                  `forall b. a -> b -> a` (if `prepend` is False)
--
-- Whether you want `prepend` to be True or False depends on the situation.
-- When reifying an entire type class, like C, one does not need to prepend a
-- class context to each of the bundled method types (see the comments for
-- quantifyClassDecMethods), so False is appropriate. When one is only reifying
-- a single class method, like `method`, then one needs the class context to
-- appear in the reified type, so `True` is appropriate.
quantifyClassMethodType
  :: Name            -- ^ The class name.
  -> [TyVarBndrUnit] -- ^ The class's type variable binders.
  -> Bool            -- ^ If 'True', prepend a class predicate.
  -> Type            -- ^ The method type.
  -> Type
quantifyClassMethodType cls_name cls_tvbs prepend meth_ty =
  add_cls_cxt quantified_meth_ty
  where
    add_cls_cxt :: Type -> Type
    add_cls_cxt
      | prepend   = ForallT (changeTVFlags SpecifiedSpec all_cls_tvbs) cls_cxt
      | otherwise = id

    cls_cxt :: Cxt
#if __GLASGOW_HASKELL__ < 709
    cls_cxt = [ClassP cls_name (map tvbToType cls_tvbs)]
#else
    cls_cxt = [foldl AppT (ConT cls_name) (map tvbToType cls_tvbs)]
#endif

    quantified_meth_ty :: Type
    quantified_meth_ty
      | null meth_tvbs
      = meth_ty
      | ForallT meth_tvbs' meth_ctxt meth_tau <- meth_ty
      = ForallT (meth_tvbs ++ meth_tvbs') meth_ctxt meth_tau
      | otherwise
      = ForallT meth_tvbs [] meth_ty

    meth_tvbs :: [TyVarBndrSpec]
    meth_tvbs = changeTVFlags SpecifiedSpec $
                deleteFirstsBy ((==) `on` tvName)
                  (freeVariablesWellScoped [meth_ty]) all_cls_tvbs

    -- Explicitly quantify any kind variables bound by the class, if any.
    all_cls_tvbs :: [TyVarBndrUnit]
    all_cls_tvbs = freeVariablesWellScoped $ map tvbToTypeWithSig cls_tvbs

stripInstanceDec :: Dec -> Dec
#if __GLASGOW_HASKELL__ >= 711
stripInstanceDec (InstanceD over cxt ty _) = InstanceD over cxt ty []
#else
stripInstanceDec (InstanceD cxt ty _)      = InstanceD cxt ty []
#endif
stripInstanceDec dec                       = dec

mkArrows :: [Type] -> Type -> Type
mkArrows []     res_ty = res_ty
mkArrows (t:ts) res_ty = AppT (AppT ArrowT t) $ mkArrows ts res_ty

maybeForallT :: [TyVarBndrUnit] -> Cxt -> Type -> Type
maybeForallT tvbs cxt ty
  | null tvbs && null cxt        = ty
  | ForallT tvbs2 cxt2 ty2 <- ty = ForallT (tvbs_spec ++ tvbs2) (cxt ++ cxt2) ty2
  | otherwise                    = ForallT tvbs_spec cxt ty
  where
    tvbs_spec = changeTVFlags SpecifiedSpec tvbs

findCon :: Name -> [Con] -> Maybe (Named Con)
findCon n = firstMatch match_con
  where
    match_con :: Con -> Maybe (Named Con)
    match_con con =
      case con of
        NormalC n' _  | n `nameMatches` n' -> Just (n', con)
        RecC n' _     | n `nameMatches` n' -> Just (n', con)
        InfixC _ n' _ | n `nameMatches` n' -> Just (n', con)
        ForallC _ _ c -> case match_con c of
                           Just (n', _) -> Just (n', con)
                           Nothing      -> Nothing
#if __GLASGOW_HASKELL__ > 710
        GadtC nms _ _    -> gadt_case con nms
        RecGadtC nms _ _ -> gadt_case con nms
#endif
        _                -> Nothing

#if __GLASGOW_HASKELL__ > 710
    gadt_case :: Con -> [Name] -> Maybe (Named Con)
    gadt_case con nms = case find (n `nameMatches`) nms of
                          Just n' -> Just (n', con)
                          Nothing -> Nothing
#endif

data RecSelInfo
  = RecSelH98  Type -- The record field's type
  | RecSelGADT Type -- The record field's type
               Type -- The GADT return type

findRecSelector :: Name -> [Con] -> Maybe (Named RecSelInfo)
findRecSelector n = firstMatch match_con
  where
    match_con :: Con -> Maybe (Named RecSelInfo)
    match_con (RecC _ vstys)            = fmap (liftSnd RecSelH98) $
                                          firstMatch match_rec_sel vstys
#if __GLASGOW_HASKELL__ >= 800
    match_con (RecGadtC _ vstys ret_ty) = fmap (liftSnd (`RecSelGADT` ret_ty)) $
                                          firstMatch match_rec_sel vstys
#endif
    match_con (ForallC _ _ c)           = match_con c
    match_con _                         = Nothing

    match_rec_sel (n', _, sel_ty)
      | n `nameMatches` n' = Just (n', sel_ty)
    match_rec_sel _        = Nothing

---------------------------------
-- Reifying fixities
---------------------------------
--
-- This section allows GHC 7.x to call reifyFixity

#if __GLASGOW_HASKELL__ < 711
qReifyFixity :: Quasi m => Name -> m (Maybe Fixity)
qReifyFixity name = do
  info <- qReify name
  return $ case info of
    ClassOpI _ _ _ fixity -> Just fixity
    DataConI _ _ _ fixity -> Just fixity
    VarI _ _ _ fixity     -> Just fixity
    _                     -> Nothing

{- | @reifyFixity nm@ attempts to find a fixity declaration for @nm@. For
example, if the function @foo@ has the fixity declaration @infixr 7 foo@, then
@reifyFixity 'foo@ would return @'Just' ('Fixity' 7 'InfixR')@. If the function
@bar@ does not have a fixity declaration, then @reifyFixity 'bar@ returns
'Nothing', so you may assume @bar@ has 'defaultFixity'.
-}
reifyFixity :: Name -> Q (Maybe Fixity)
reifyFixity = qReifyFixity
#endif

-- | Like 'reifyWithLocals_maybe', but for fixities. Note that a return value
-- of @Nothing@ might mean that the name is not in scope, or it might mean
-- that the name has no assigned fixity. (Use 'reifyWithLocals_maybe' if
-- you really need to tell the difference.)
reifyFixityWithLocals :: DsMonad q => Name -> q (Maybe Fixity)
reifyFixityWithLocals name = qRecover
  (return . reifyFixityInDecs name =<< localDeclarations)
  (qReifyFixity name)

--------------------------------------
-- Reifying types
--------------------------------------
--
-- This section allows GHC <8.9 to call reifyFixity

#if __GLASGOW_HASKELL__ < 809
qReifyType :: forall m. Quasi m => Name -> m Type
qReifyType name = do
  info <- qReify name
  case infoType info <|> info_kind info of
    Just t  -> return t
    Nothing -> fail $ "Could not reify the full type of " ++ nameBase name
  where
    info_kind :: Info -> Maybe Kind
    info_kind info = do
      dec <- case info of
               ClassI d _  -> Just d
               TyConI d    -> Just d
               FamilyI d _ -> Just d
               _           -> Nothing
      match_cusk name dec

{- | @reifyType nm@ attempts to find the type or kind of @nm@. For example,
@reifyType 'not@   returns @Bool -> Bool@, and
@reifyType ''Bool@ returns @Type@.
This works even if there's no explicit signature and the type or kind is inferred.
-}
reifyType :: Name -> Q Type
reifyType = qReifyType
#endif

-- | Like 'reifyTypeWithLocals_maybe', but throws an exception upon failure,
-- warning the user about separating splices.
reifyTypeWithLocals :: DsMonad q => Name -> q Type
reifyTypeWithLocals name = do
  m_info <- reifyTypeWithLocals_maybe name
  case m_info of
    Nothing -> reifyFail name
    Just i  -> return i

-- | Like 'reifyWithLocals_maybe' but for types and kinds. Note that a return
-- value of @Nothing@ might mean that the name is not in scope, or it might
-- mean that the full type of the name cannot be determined. (Use
-- 'reifyWithLocals_maybe' if you really need to tell the difference.)
reifyTypeWithLocals_maybe :: DsMonad q => Name -> q (Maybe Type)
reifyTypeWithLocals_maybe name = do
#if __GLASGOW_HASKELL__ >= 809
  cusks <- qIsExtEnabled CUSKs
#else
  -- On earlier GHCs, the behavior of -XCUSKs was the norm.
  let cusks = True
#endif
  qRecover (return . reifyTypeInDecs cusks name =<< localDeclarations)
           (Just `fmap` qReifyType name)

-- | Look through a list of declarations and return its full type, if
-- available.
reifyTypeInDecs :: Bool -> Name -> [Dec] -> Maybe Type
reifyTypeInDecs cusks name decs =
  (reifyInDecs name decs >>= infoType) <|> findKind cusks name decs

-- Extract the type information (if any) contained in an Info.
infoType :: Info -> Maybe Type
infoType info =
  case info of
    ClassOpI _ t _
#if __GLASGOW_HASKELL__ < 800
             _
#endif
                   -> Just t
    DataConI _ t _
#if __GLASGOW_HASKELL__ < 800
             _
#endif
                   -> Just t
    VarI _ t _
#if __GLASGOW_HASKELL__ < 800
         _
#endif
                   -> Just t
    TyVarI _ t     -> Just t
#if __GLASGOW_HASKELL__ >= 802
    PatSynI _ t    -> Just t
#endif
    _              -> Nothing

-- Like findType, but instead searching for kind signatures.
-- This mostly searches through `KiSigD`s, but if the -XCUSKs extension is
-- enabled, this also retrieves kinds for declarations with CUSKs.
findKind :: Bool -- Is -XCUSKs enabled?
         -> Name -> [Dec] -> Maybe Kind
findKind cusks name decls =
      firstMatch (match_kind_sig name decls) decls
  <|> whenAlt cusks (firstMatch (match_cusk name) decls)

-- Look for a declaration's kind by searching for its standalone kind
-- signature, if available.
match_kind_sig :: Name -> [Dec] -> Dec -> Maybe Kind
match_kind_sig n decs (ClassD _ n' tvbs _ sub_decs)
  -- If a class has a standalone kind signature, then we can determine the
  -- full kind of its associated types in 99% of cases.
  -- See Note [The limitations of standalone kind signatures] for what
  -- happens in the other 1% of cases.
  | Just ki <- firstMatch (find_kind_sig n') decs
  , let (arg_kis, _res_ki) = unravelType ki
        mb_vis_arg_kis     = map vis_arg_kind_maybe $ filterVisFunArgs arg_kis
        cls_tvb_kind_map   =
          Map.fromList [ (tvName tvb, tvb_kind)
                       | (tvb, mb_vis_arg_ki) <- zip tvbs mb_vis_arg_kis
                       , Just tvb_kind <- [mb_vis_arg_ki <|> tvb_kind_maybe tvb]
                       ]
  = firstMatch (find_assoc_type_kind n cls_tvb_kind_map) sub_decs
match_kind_sig n _ dec = find_kind_sig n dec

find_kind_sig :: Name -> Dec -> Maybe Kind
#if __GLASGOW_HASKELL__ >= 809
find_kind_sig n (KiSigD n' ki)
  | n `nameMatches` n' = Just ki
#endif
find_kind_sig _ _ = Nothing

-- Compute a declaration's kind by retrieving its CUSK, if it has one.
-- This is only done when -XCUSKs is enabled, or on older GHCs where
-- CUSKs were the only means of specifying this information.
match_cusk :: Name -> Dec -> Maybe Kind
#if __GLASGOW_HASKELL__ >= 800
match_cusk n (DataD _ n' tvbs m_ki _ _)
  | n `nameMatches` n'
  = datatype_kind tvbs m_ki
match_cusk n (NewtypeD _ n' tvbs m_ki _ _)
  | n `nameMatches` n'
  = datatype_kind tvbs m_ki
match_cusk n (DataFamilyD n' tvbs m_ki)
  | n `nameMatches` n'
  = open_ty_fam_kind tvbs m_ki
match_cusk n (OpenTypeFamilyD (TypeFamilyHead n' tvbs res_sig _))
  | n `nameMatches` n'
  = open_ty_fam_kind tvbs (res_sig_to_kind res_sig)
match_cusk n (ClosedTypeFamilyD (TypeFamilyHead n' tvbs res_sig _) _)
  | n `nameMatches` n'
  = closed_ty_fam_kind tvbs (res_sig_to_kind res_sig)
#else
match_cusk n (DataD _ n' tvbs _ _)
  | n `nameMatches` n'
  = datatype_kind tvbs Nothing
match_cusk n (NewtypeD _ n' tvbs _ _)
  | n `nameMatches` n'
  = datatype_kind tvbs Nothing
match_cusk n (FamilyD _ n' tvbs m_ki)
  | n `nameMatches` n'
  = open_ty_fam_kind tvbs m_ki
match_cusk n (ClosedTypeFamilyD n' tvbs m_ki _)
  | n `nameMatches` n'
  = closed_ty_fam_kind tvbs m_ki
#endif
match_cusk n (TySynD n' tvbs rhs)
  | n `nameMatches` n'
  = ty_syn_kind tvbs rhs
match_cusk n (ClassD _ n' tvbs _ sub_decs)
  | n `nameMatches` n'
  = class_kind tvbs
  | -- An associated type family can only have a CUSK if its parent class
    -- also has a CUSK.
    all tvb_is_kinded tvbs
  , let cls_tvb_kind_map = Map.fromList [ (tvName tvb, tvb_kind)
                                        | tvb <- tvbs
                                        , Just tvb_kind <- [tvb_kind_maybe tvb]
                                        ]
  = firstMatch (find_assoc_type_kind n cls_tvb_kind_map) sub_decs
match_cusk _ _ = Nothing

-- Uncover the kind of an associated type family. There is an invariant
-- that this function should only ever be called when the kind of the
-- parent class is known (i.e., if it has a standalone kind signature or a
-- CUSK). Despite this, it is possible for this function to return Nothing.
-- See Note [The limitations of standalone kind signatures].
find_assoc_type_kind :: Name -> Map Name Kind -> Dec -> Maybe Kind
find_assoc_type_kind n cls_tvb_kind_map sub_dec =
  case sub_dec of
#if __GLASGOW_HASKELL__ >= 800
    DataFamilyD n' tf_tvbs m_ki
      |  n `nameMatches` n'
      -> build_kind (map ascribe_tf_tvb_kind tf_tvbs) (default_res_ki m_ki)
    OpenTypeFamilyD (TypeFamilyHead n' tf_tvbs res_sig _)
      |  n `nameMatches` n'
      -> build_kind (map ascribe_tf_tvb_kind tf_tvbs)
                    (default_res_ki $ res_sig_to_kind res_sig)
#else
    FamilyD _ n' tf_tvbs m_ki
      |  n `nameMatches` n'
      -> build_kind (map ascribe_tf_tvb_kind tf_tvbs) (default_res_ki m_ki)
#endif
    _ -> Nothing
  where
    ascribe_tf_tvb_kind :: TyVarBndrUnit -> TyVarBndrUnit
    ascribe_tf_tvb_kind tvb =
      elimTV (\tvn -> kindedTV tvn $ fromMaybe StarT $ Map.lookup tvn cls_tvb_kind_map)
             (\_ _ -> tvb)
             tvb

-- Data types have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. All kind variables in the result kind are explicitly quantified.
datatype_kind :: [TyVarBndrUnit] -> Maybe Kind -> Maybe Kind
datatype_kind tvbs m_ki =
  whenAlt (all tvb_is_kinded tvbs && ki_fvs_are_bound) $
  build_kind tvbs (default_res_ki m_ki)
  where
    ki_fvs_are_bound :: Bool
    ki_fvs_are_bound =
      let ki_fvs   = Set.fromList $ foldMap freeVariables m_ki
          tvb_vars = Set.fromList $ freeVariables $ map tvbToTypeWithSig tvbs
      in ki_fvs `Set.isSubsetOf` tvb_vars

-- Classes have CUSKs when all of their type variables have explicit kinds.
class_kind :: [TyVarBndrUnit] -> Maybe Kind
class_kind tvbs = whenAlt (all tvb_is_kinded tvbs) $
                  build_kind tvbs ConstraintT

-- Open type families and data families always have CUSKs. Type variables
-- without explicit kinds default to Type, as does the return kind if it
-- is not specified.
open_ty_fam_kind :: [TyVarBndrUnit] -> Maybe Kind -> Maybe Kind
open_ty_fam_kind tvbs m_ki =
  build_kind (map default_tvb tvbs) (default_res_ki m_ki)

-- Closed type families have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. An explicit return kind is supplied.
closed_ty_fam_kind :: [TyVarBndrUnit] -> Maybe Kind -> Maybe Kind
closed_ty_fam_kind tvbs m_ki =
  case m_ki of
    Just ki -> whenAlt (all tvb_is_kinded tvbs) $
               build_kind tvbs ki
    Nothing -> Nothing

-- Type synonyms have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. The right-hand-side type is annotated with an explicit kind.
ty_syn_kind :: [TyVarBndrUnit] -> Type -> Maybe Kind
ty_syn_kind tvbs rhs =
  case rhs of
    SigT _ ki -> whenAlt (all tvb_is_kinded tvbs) $
                 build_kind tvbs ki
    _         -> Nothing

-- Attempt to construct the full kind of a type-level declaration from its
-- type variable binders and return kind. Do note that the result type of
-- this function is `Maybe Kind` because there are situations where even
-- this amount of information is not sufficient to determine the full kind.
-- See Note [The limitations of standalone kind signatures].
build_kind :: [TyVarBndrUnit] -> Kind -> Maybe Kind
build_kind arg_kinds res_kind =
  fmap quantifyType $ fst $
  foldr go (Just res_kind, Set.fromList (freeVariables res_kind)) arg_kinds
  where
    go :: TyVarBndrUnit -> (Maybe Kind, Set Name) -> (Maybe Kind, Set Name)
    go tvb (res, res_fvs) =
      elimTV (\n ->
               ( if n `Set.member` res_fvs
                 then forall_vis tvb res
                 else Nothing -- We have a type variable binder without an
                              -- explicit kind that is not used dependently, so
                              -- we cannot build a kind from it. This is the
                              -- only case where we return Nothing.
               , res_fvs
               ))
             (\n k ->
               ( if n `Set.member` res_fvs
                 then forall_vis tvb res
                 else fmap (ArrowT `AppT` k `AppT`) res
               , Set.fromList (freeVariables k) `Set.union` res_fvs
               ))
             tvb

    forall_vis :: TyVarBndrUnit -> Maybe Kind -> Maybe Kind
#if __GLASGOW_HASKELL__ >= 809
    forall_vis tvb m_ki = fmap (ForallVisT [tvb]) m_ki
      -- One downside of this approach is that we generate kinds like this:
      --
      --   forall a -> forall b -> forall c -> (a, b, c)
      --
      -- Instead of this more compact kind:
      --
      --   forall a b c -> (a, b, c)
      --
      -- Thankfully, the difference is only cosmetic.
#else
    forall_vis _   _    = Nothing
#endif

tvb_is_kinded :: TyVarBndr_ flag -> Bool
tvb_is_kinded = isJust . tvb_kind_maybe

tvb_kind_maybe :: TyVarBndr_ flag -> Maybe Kind
tvb_kind_maybe = elimTV (\_ -> Nothing) (\_ k -> Just k)

vis_arg_kind_maybe :: VisFunArg -> Maybe Kind
vis_arg_kind_maybe (VisFADep tvb) = tvb_kind_maybe tvb
vis_arg_kind_maybe (VisFAAnon k)  = Just k

default_tvb :: TyVarBndrUnit -> TyVarBndrUnit
default_tvb tvb = elimTV (\n -> kindedTV n StarT) (\_ _ -> tvb) tvb

default_res_ki :: Maybe Kind -> Kind
default_res_ki = fromMaybe StarT

#if __GLASGOW_HASKELL__ >= 800
res_sig_to_kind :: FamilyResultSig -> Maybe Kind
res_sig_to_kind NoSig          = Nothing
res_sig_to_kind (KindSig k)    = Just k
res_sig_to_kind (TyVarSig tvb) = tvb_kind_maybe tvb
#endif

whenAlt :: Alternative f => Bool -> f a -> f a
whenAlt b fa = if b then fa else empty

{-
Note [The limitations of standalone kind signatures]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
A current limitation of StandaloneKindSignatures is that they cannot be applied
to associated type families. This can have some surprising consequences.
Consider the following code, taken from
https://gitlab.haskell.org/ghc/ghc/issues/17072#note_221324:

  type C :: forall a -> a -> Constraint
  class C a b where
    type T a :: Type

The parent class C has a standalone kind signature, so GHC treats its
associated types as if they had CUSKs. Can th-desugar figure out the kind
that GHC gives to T?

Unfortunately, the answer is "not easily". This is because `type T a` says
nothing about the kind of `a`, so th-desugar's only other option is to inspect
the kind signature for C. Even this is for naught, as the `forall a -> ...`
part doesn't state the kind of `a` either! The only way to know that the kind
of `a` should be Type is to infer that from the rest of the kind
(`a -> Constraint`), but this gets perilously close to requiring full kind
inference, which is rather unwieldy in Template Haskell.

In cases like T, we simply give up and return Nothing when trying to reify
its kind. It's not ideal, but them's the breaks when you try to extract kinds
from syntax. There is a rather simple workaround available: just write
`type C :: forall (a :: Type) -> a -> Constraint` instead.
-}

--------------------------------------
-- Looking up name value and type names
--------------------------------------

-- | Like 'lookupValueName' from Template Haskell, but looks also in 'Names' of
-- not-yet-typechecked declarations. To establish this list of not-yet-typechecked
-- declarations, use 'withLocalDeclarations'. Returns 'Nothing' if no value
-- with the same name can be found.
lookupValueNameWithLocals :: DsMonad q => String -> q (Maybe Name)
lookupValueNameWithLocals = lookupNameWithLocals False

-- | Like 'lookupTypeName' from Template Haskell, but looks also in 'Names' of
-- not-yet-typechecked declarations. To establish this list of not-yet-typechecked
-- declarations, use 'withLocalDeclarations'. Returns 'Nothing' if no type
-- with the same name can be found.
lookupTypeNameWithLocals :: DsMonad q => String -> q (Maybe Name)
lookupTypeNameWithLocals = lookupNameWithLocals True

lookupNameWithLocals :: DsMonad q => Bool -> String -> q (Maybe Name)
lookupNameWithLocals ns s = do
    mb_name <- qLookupName ns s
    case mb_name of
      j_name@(Just{}) -> return j_name
      Nothing         -> consult_locals
  where
    built_name = mkName s

    consult_locals = do
      decs <- localDeclarations
      let mb_infos = map (reifyInDec built_name decs) decs
          infos = catMaybes mb_infos
      return $ firstMatch (if ns then find_type_name
                                 else find_value_name) infos

    -- These functions work over Named Infos so we can avoid performing
    -- tiresome pattern-matching to retrieve the name associated with each Info.
    find_type_name, find_value_name :: Named Info -> Maybe Name
    find_type_name (n, info) =
      case infoNameSpace info of
        TcClsName -> Just n
        VarName   -> Nothing
        DataName  -> Nothing

    find_value_name (n, info) =
      case infoNameSpace info of
        VarName   -> Just n
        DataName  -> Just n
        TcClsName -> Nothing

-- | Like TH's @lookupValueName@, but if this name is not bound, then we assume
-- it is declared in the current module.
--
-- Unlike 'mkDataName', this also consults the local declarations in scope when
-- determining if the name is currently bound.
mkDataNameWithLocals :: DsMonad q => String -> q Name
mkDataNameWithLocals = mkNameWith lookupValueNameWithLocals mkNameG_d

-- | Like TH's @lookupTypeName@, but if this name is not bound, then we assume
-- it is declared in the current module.
--
-- Unlike 'mkTypeName', this also consults the local declarations in scope when
-- determining if the name is currently bound.
mkTypeNameWithLocals :: DsMonad q => String -> q Name
mkTypeNameWithLocals = mkNameWith lookupTypeNameWithLocals mkNameG_tc

-- | Determines a `Name`'s 'NameSpace'. If the 'NameSpace' is attached to
-- the 'Name' itself (i.e., it is unambiguous), then that 'NameSpace' is
-- immediately returned. Otherwise, reification is used to lookup up the
-- 'NameSpace' (consulting local declarations if necessary).
--
-- Note that if a 'Name' lives in two different 'NameSpaces' (which can
-- genuinely happen--for instance, @'mkName' \"==\"@, where @==@ is both
-- a function and a type family), then this function will simply return
-- whichever 'NameSpace' is discovered first via reification. If you wish
-- to find a 'Name' in a particular 'NameSpace', use the
-- 'lookupValueNameWithLocals' or 'lookupTypeNameWithLocals' functions.
reifyNameSpace :: DsMonad q => Name -> q (Maybe NameSpace)
reifyNameSpace n@(Name _ nf) =
  case nf of
    -- NameGs are simple, as they have a NameSpace attached.
    NameG ns _ _ -> pure $ Just ns

    -- For other names, we must use reification to determine what NameSpace
    -- it lives in (if any).
    _ -> do mb_info <- reifyWithLocals_maybe n
            pure $ fmap infoNameSpace mb_info

-- | Determine a name's 'NameSpace' from its 'Info'.
infoNameSpace :: Info -> NameSpace
infoNameSpace info =
  case info of
    ClassI{}     -> TcClsName
    TyConI{}     -> TcClsName
    FamilyI{}    -> TcClsName
    PrimTyConI{} -> TcClsName
    TyVarI{}     -> TcClsName

    ClassOpI{}   -> VarName
    VarI{}       -> VarName

    DataConI{}   -> DataName
#if __GLASGOW_HASKELL__ >= 801
    PatSynI{}    -> DataName
#endif
