{- Language/Haskell/TH/Desugar/Reify.hs

(c) Richard Eisenberg 2014
rae@cs.brynmawr.edu

Allows for reification from a list of declarations, without looking a name
up in the environment.
-}

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving, ScopedTypeVariables,
             TupleSections #-}

module Language.Haskell.TH.Desugar.Reify (
  -- * Reification
  reifyWithLocals_maybe, reifyWithLocals, reifyWithWarning,

  -- ** Fixity reification
  qReifyFixity, reifyFixity, reifyFixityWithLocals,

  -- ** Type reification
  qReifyType, reifyType,
  reifyTypeWithLocals_maybe, reifyTypeWithLocals,

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
import Data.Coerce
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
  (return . Map.lookup (ReifiableName name) =<< localInfoMap)
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
         -> q ([TyVarBndr], [Con])
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
mkExtraKindBinders :: forall q. Quasi q => Kind -> q [TyVarBndr]
mkExtraKindBinders k = do
  k' <- runQ $ resolveTypeSynonyms k
  let (fun_args, _) = unravelType k'
      vis_fun_args  = filterVisFunArgs fun_args
  mapM mk_tvb vis_fun_args
  where
    mk_tvb :: VisFunArg -> q TyVarBndr
    mk_tvb (VisFADep tvb) = return tvb
    mk_tvb (VisFAAnon ki) = KindedTV <$> qNewName "a" <*> return ki

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
  let m_con = find (any (con_name ==) . conNames) cons
  case m_con of
    Just con -> return con
    Nothing -> impossible "Datatype does not contain one of its own constructors."

--------------------------------------------------
-- DsMonad
--------------------------------------------------

-- | A 'DsMonad' stores some list of declarations that should be considered
-- in scope. 'DsM' is the prototypical inhabitant of 'DsMonad'.
class (Quasi m, Fail.MonadFail m) => DsMonad m where
  -- | Produce a list of local declarations.
  localDeclarations :: m [Dec]

  -- | TODO RGS: Docs
  localInfoMap :: m (Map ReifiableName Info)

  -- | TODO RGS: Decs
  localInstancesMap :: m (Map ReifiableName [InstanceDec])

  -- | TODO RGS: Docs
  localFixityMap :: m (Map ReifiableName Fixity)

  -- | TODO RGS: Docs
  localTypeMap :: m (Map ReifiableName Type)

instance DsMonad Q where
  localDeclarations = return []
  localInfoMap      = return Map.empty
  localInstancesMap = return Map.empty
  localFixityMap    = return Map.empty
  localTypeMap      = return Map.empty

instance DsMonad IO where
  localDeclarations = return []
  localInfoMap      = return Map.empty
  localInstancesMap = return Map.empty
  localFixityMap    = return Map.empty
  localTypeMap      = return Map.empty

-- | TODO RGS: Docs
data DsEnv = DsEnv
  { dsEnvDecs         :: [Dec]
  , dsEnvInfoMap      :: Map ReifiableName Info
  , dsEnvInstancesMap :: Map ReifiableName [InstanceDec]
  , dsEnvFixityMap    :: Map ReifiableName Fixity
  , dsEnvTypeMap      :: Map ReifiableName Type
  }

-- | A convenient implementation of the 'DsMonad' class. Use by calling
-- 'withLocalDeclarations'.
newtype DsM q a = DsM (ReaderT DsEnv q a)
  deriving ( Functor, Applicative, Monad, MonadTrans, Quasi, Fail.MonadFail
#if __GLASGOW_HASKELL__ >= 803
           , MonadIO
#endif
           )

instance (Quasi q, Fail.MonadFail q) => DsMonad (DsM q) where
  localDeclarations = DsM $ asks dsEnvDecs
  localInfoMap      = DsM $ asks dsEnvInfoMap
  localInstancesMap = DsM $ asks dsEnvInstancesMap
  localFixityMap    = DsM $ asks dsEnvFixityMap
  localTypeMap      = DsM $ asks dsEnvTypeMap

instance DsMonad m => DsMonad (ReaderT r m) where
  localDeclarations = lift localDeclarations
  localInfoMap      = lift localInfoMap
  localInstancesMap = lift localInstancesMap
  localFixityMap    = lift localFixityMap
  localTypeMap      = lift localTypeMap

instance DsMonad m => DsMonad (StateT s m) where
  localDeclarations = lift localDeclarations
  localInfoMap      = lift localInfoMap
  localInstancesMap = lift localInstancesMap
  localFixityMap    = lift localFixityMap
  localTypeMap      = lift localTypeMap

instance (DsMonad m, Monoid w) => DsMonad (WriterT w m) where
  localDeclarations = lift localDeclarations
  localInfoMap      = lift localInfoMap
  localInstancesMap = lift localInstancesMap
  localFixityMap    = lift localFixityMap
  localTypeMap      = lift localTypeMap

instance (DsMonad m, Monoid w) => DsMonad (RWST r w s m) where
  localDeclarations = lift localDeclarations
  localInfoMap      = lift localInfoMap
  localInstancesMap = lift localInstancesMap
  localFixityMap    = lift localFixityMap
  localTypeMap      = lift localTypeMap

-- | Add a list of declarations to be considered when reifying local
-- declarations.
withLocalDeclarations :: DsMonad q => [Dec] -> DsM q a -> q a
withLocalDeclarations new_decs (DsM x) = do
  cusks <- cusksEnabled

  old_decs          <- localDeclarations
  old_info_map      <- localInfoMap
  old_instances_map <- localInstancesMap
  old_fixity_map    <- localFixityMap
  old_type_map      <- localTypeMap
  let new_fixity_map    = filterFixities new_decs
      new_instances_map = filterInstanceDecs new_decs
      new_type_map      = filterTypes cusks new_decs
      new_info_map      = filterInfos new_fixity_map new_instances_map
                                      new_type_map new_decs

      unioned_fixity_map    = union_locals old_fixity_map new_fixity_map
                              -- TODO RGS: Why Map.unionWith (++) here?
      unioned_info_map      = union_locals old_info_map new_info_map
      unioned_instances_map = Map.unionWith (++) old_instances_map new_instances_map
      unioned_type_map      = union_locals old_type_map new_type_map

      env' = DsEnv { -- Note how we append new local declarations to the right
                     -- of existing ones. See Note [TODO RGS].
                     --
                     -- This is not as efficient as it could be, but it will
                     -- only ever cause problems if one repeatedly nests uses
                     -- of `withLocalDeclarations`. This is fairly uncommon,
                     -- however, so I won't bother improving this unless
                     -- someone asks for it.
                     dsEnvDecs         = old_decs ++ new_decs
                   , dsEnvInfoMap      = unioned_info_map
                   , dsEnvInstancesMap = unioned_instances_map
                   , dsEnvFixityMap    = unioned_fixity_map
                   , dsEnvTypeMap      = unioned_type_map
                   }
  runReaderT x env'
  where
    -- TODO RGS: Docs. Also, should duplicate entries be an error?
    union_locals :: Map ReifiableName a -> Map ReifiableName a -> Map ReifiableName a
    union_locals old_map new_map = Map.union old_map new_map

conNames :: Con -> [Name]
conNames (NormalC name _)     = [name]
conNames (RecC name _)        = [name]
conNames (InfixC _ name _)    = [name]
conNames (ForallC _ _ con)    = conNames con
#if __GLASGOW_HASKELL__ >= 800
conNames (GadtC names _ _)    = names
conNames (RecGadtC names _ _) = names
#endif

recSelNames :: Con -> [Name]
recSelNames NormalC{}            = []
recSelNames InfixC{}             = []
recSelNames (RecC _ vstys)       = map (\(n,_,_) -> n) vstys
recSelNames (ForallC _ _ c)      = recSelNames c
#if __GLASGOW_HASKELL__ >= 800
recSelNames GadtC{}              = []
recSelNames (RecGadtC _ vstys _) = map (\(n,_,_) -> n) vstys
#endif

foreignName :: Foreign -> Name
foreignName (ImportF _ _ _ n _) = n
foreignName (ExportF _ _ n _)   = n

---------------------------
-- Reifying local declarations
---------------------------

-- | A reified thing along with the name of that thing.
type Named a = (Name, a)

mk_reifiable_name_map :: [Named a] -> Map ReifiableName a
mk_reifiable_name_map = Map.fromList . coerce

-- | TODO RGS: Docs
filterFixities :: [Dec] -> Map ReifiableName Fixity
filterFixities = mk_reifiable_name_map . concatMap filter_fixities
  where
    filter_fixities :: Dec -> [Named Fixity]
    filter_fixities (InfixD fixity n)         = [(n, fixity)]
    filter_fixities (ClassD _ _ _ _ sub_decs) = concatMap filter_fixities sub_decs
    filter_fixities _                         = []

-- | TODO RGS: Docs
filterInfos :: Map ReifiableName Fixity
            -> Map ReifiableName [InstanceDec]
            -> Map ReifiableName Type
            -> [Dec] -> Map ReifiableName Info
filterInfos fixity_map instances_map type_map =
  mk_reifiable_name_map . concatMap filter_infos
  where
    filter_infos :: Dec -> [Named Info]
    filter_infos (FunD n _) =
      [(n, mk_var_i n)]
    filter_infos (ValD pat _ _) =
      map (\n -> (n, mk_var_i n)) (F.toList $ extractBoundNamesPat pat)
    filter_infos dec@(TySynD n _ _) =
      [(n, TyConI dec)]
    filter_infos dec@(ClassD _ n _ _ sub_decs) =
      (n, mkClassI instances_map n dec) : concatMap (filter_class_sub_dec_infos n) sub_decs
    filter_infos (InstanceD
#if __GLASGOW_HASKELL__ >= 800
                            _
#endif
                            _ _ sub_decs) =
      concatMap filter_instance_sub_dec_infos sub_decs
    filter_infos (ForeignD fgn) =
      let n = foreignName fgn in [(n, mk_var_i n)]
    filter_infos dec@(DataD _ n _
#if __GLASGOW_HASKELL__ >= 800
                            _
#endif
                            cons _) =
      (n, TyConI dec) : concatMap (con_infos n) cons
    filter_infos dec@(NewtypeD _ n _
#if __GLASGOW_HASKELL__ >= 800
                               _
#endif
                               con _) =
      (n, TyConI dec) : con_infos n con
#if __GLASGOW_HASKELL__ >= 800
    filter_infos dec@(DataFamilyD n _ _) =
      [(n, mk_family_i n dec)]
    filter_infos dec@(OpenTypeFamilyD (TypeFamilyHead n _ _ _)) =
      [(n, mk_family_i n dec)]
    filter_infos dec@(ClosedTypeFamilyD (TypeFamilyHead n _ _ _) _) =
      [(n, mk_family_i n dec)]
#else
    filter_infos dec@(FamilyD _ n _ _) =
      [(n, mk_family_i n dec)]
    filter_infos dec@(ClosedTypeFamilyD n _ _ _) =
      [(n, mk_family_i n dec)]
#endif
#if __GLASGOW_HASKELL__ >= 808
    filter_infos (DataInstD _ _ lhs _ cons _)
      | (ConT n, _) <- unfoldType lhs
      = concatMap (con_infos n) cons
    filter_infos (NewtypeInstD _ _ lhs _ con _)
      | (ConT n, _) <- unfoldType lhs
      = con_infos n con
#else
    filter_infos (DataInstD _ n _
#if __GLASGOW_HASKELL__ >= 800
                            _
#endif
                            cons _)
      = concatMap (con_infos n) cons
    filter_infos (NewtypeInstD _ n _
#if __GLASGOW_HASKELL__ >= 800
                               _
#endif
                               con _)
      = con_infos n con
#endif
#if __GLASGOW_HASKELL__ >= 802
    filter_infos (PatSynD n _ _ _) =
      [(n, mkPatSynI type_map n)]
#endif
    filter_infos _ = []

    filter_class_sub_dec_infos :: Name -> Dec -> [Named Info]
    filter_class_sub_dec_infos cls_name sub_dec =
      case sub_dec of
        SigD meth_name _  ->
          [(meth_name, mkClassOpI fixity_map type_map cls_name meth_name)]
#if __GLASGOW_HASKELL__ >= 800
        DataFamilyD{}     -> filter_infos sub_dec
        OpenTypeFamilyD{} -> filter_infos sub_dec
#else
        FamilyD{}         -> filter_infos sub_dec
#endif
        _                 -> []

    filter_instance_sub_dec_infos :: Dec -> [Named Info]
    filter_instance_sub_dec_infos dec@DataInstD{}    = filter_infos dec
    filter_instance_sub_dec_infos dec@NewtypeInstD{} = filter_infos dec
    filter_instance_sub_dec_infos _                  = []

    mk_var_i    = mkVarI fixity_map type_map
    mk_family_i = mkFamilyI instances_map

    con_infos :: Name -> Con -> [Named Info]
    con_infos data_name con =
         map (\con_name -> (con_name, mkDataConI fixity_map type_map data_name con_name)) (conNames con)
      ++ map (\sel_name -> (sel_name, mk_var_i sel_name)) (recSelNames con)

{-
Note [Use unSigType in filterTypes]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Make sure to call unSigType on the type of a reified data constructor or
record selector. Otherwise, if you have this:

  data D (a :: k) = MkD { unD :: Proxy a }

Then the type of unD will be reified as:

  unD :: forall k (a :: k). D (a :: k) -> Proxy a

This is contrast to GHC's own reification, which will produce `D a`
(without the explicit kind signature) as the type of the first argument.
-}

-- Reverse-engineer the type of a data constructor.
con_to_type :: [TyVarBndr] -- The type variables bound by a data type head.
                           -- Only used for Haskell98-style constructors.
            -> Type        -- The constructor result type.
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

mkVarI :: Map ReifiableName Fixity -> Map ReifiableName Type
       -> Name -> Info
mkVarI _fixity_map type_map n =
  VarI n (fromMaybe (no_type n) $ Map.lookup (coerce n) type_map) Nothing
#if __GLASGOW_HASKELL__ < 800
       (fromMaybe defaultFixity $ Map.lookup (coerce n) _fixity_map)
#endif

mkDataConI :: Map ReifiableName Fixity -> Map ReifiableName Type -> Name
           -> Name -> Info
mkDataConI _fixity_map type_map data_name con_name =
  DataConI con_name (fromMaybe (no_type con_name) $ Map.lookup (coerce con_name) type_map) data_name
#if __GLASGOW_HASKELL__ < 800
                    (fromMaybe defaultFixity $ Map.lookup (coerce con_name) _fixity_map)
#endif

mkFamilyI :: Map ReifiableName [InstanceDec] -> Name -> Dec -> Info
mkFamilyI instances_map n dec =
  FamilyI dec (fromMaybe [] $ Map.lookup (coerce n) instances_map)

mkClassI :: Map ReifiableName [InstanceDec] -> Name -> Dec -> Info
mkClassI instances_map n dec =
  ClassI (quantifyClassDecMethods dec) (fromMaybe [] $ Map.lookup (coerce n) instances_map)

mkClassOpI :: Map ReifiableName Fixity -> Map ReifiableName Type -> Name
           -> Name -> Info
mkClassOpI _fixity_map type_map cls_name meth_name =
  ClassOpI meth_name (fromMaybe (no_type meth_name) $ Map.lookup (coerce meth_name) type_map) cls_name
#if __GLASGOW_HASKELL__ < 800
           (fromMaybe defaultFixity $ Map.lookup (coerce meth_name) _fixity_map)
#endif

#if __GLASGOW_HASKELL__ >= 802
mkPatSynI :: Map ReifiableName Type -> Name -> Info
mkPatSynI type_map n = PatSynI n (fromMaybe (no_type n) $ Map.lookup (coerce n) type_map)
#endif

no_type :: Name -> Type
no_type n = error $ "No type information found in local declaration for "
                    ++ show n

-- | TODO RGS: Docs.
filterInstanceDecs :: [Dec] -> Map ReifiableName [InstanceDec]
filterInstanceDecs =
    F.foldl' (Map.unionWith (++)) Map.empty
  . map (\(n, d) -> Map.singleton (ReifiableName n) [stripInstanceDec d])
  . concatMap filter_instance_decs
  where
    filter_instance_decs :: Dec -> [Named InstanceDec]
#if __GLASGOW_HASKELL__ >= 800
    filter_instance_decs d@(InstanceD _ _ ty sub_decs)
#else
    filter_instance_decs d@(InstanceD _ ty sub_decs)
#endif
      = maybeToList m_dec_entry ++ concatMap filter_instance_decs sub_decs
      where
        m_dec_entry = case ty_head ty of
                        ConT n -> Just (n, d)
                        _      -> Nothing
#if __GLASGOW_HASKELL__ >= 808
    filter_instance_decs (DataInstD ctxt _ lhs mk cons derivs)
      | ConT n <- ty_head lhs
      = [(n, d)]
      where
        mtvbs = rejig_data_inst_tvbs ctxt lhs mk
        d = DataInstD ctxt mtvbs lhs mk cons derivs
    filter_instance_decs (NewtypeInstD ctxt _ lhs mk con derivs)
      | ConT n <- ty_head lhs
      = [(n, d)]
      where
        mtvbs = rejig_data_inst_tvbs ctxt lhs mk
        d = NewtypeInstD ctxt mtvbs lhs mk con derivs
#elif __GLASGOW_HASKELL__ >= 800
    filter_instance_decs d@(DataInstD _ n _ _ _ _)    = [(n, d)]
    filter_instance_decs d@(NewtypeInstD _ n _ _ _ _) = [(n, d)]
#else
    filter_instance_decs d@(DataInstD _ n _ _ _)      = [(n, d)]
    filter_instance_decs d@(NewtypeInstD _ n _ _ _)   = [(n, d)]
#endif
#if __GLASGOW_HASKELL__ >= 808
    filter_instance_decs (TySynInstD (TySynEqn _ lhs rhs))
      | ConT n <- ty_head lhs
      = [(n, d)]
      where
        mtvbs = rejig_tvbs [lhs, rhs]
        d = TySynInstD (TySynEqn mtvbs lhs rhs)
#else
    filter_instance_decs d@(TySynInstD n _) = [(n, d)]
#endif
    filter_instance_decs _ = []

#if __GLASGOW_HASKELL__ >= 807
    -- See Note [Rejigging reified type family equations variable binders]
    -- for why this is necessary.
    rejig_tvbs :: [Type] -> Maybe [TyVarBndr]
    rejig_tvbs ts =
      let tvbs = freeVariablesWellScoped ts
      in if null tvbs
         then Nothing
         else Just tvbs

    rejig_data_inst_tvbs :: Cxt -> Type -> Maybe Kind -> Maybe [TyVarBndr]
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
  :: Name        -- ^ The class name.
  -> [TyVarBndr] -- ^ The class's type variable binders.
  -> Bool        -- ^ If 'True', prepend a class predicate.
  -> Type        -- ^ The method type.
  -> Type
quantifyClassMethodType cls_name cls_tvbs prepend meth_ty =
  add_cls_cxt quantified_meth_ty
  where
    add_cls_cxt :: Type -> Type
    add_cls_cxt
      | prepend   = ForallT all_cls_tvbs cls_cxt
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

    meth_tvbs :: [TyVarBndr]
    meth_tvbs = deleteFirstsBy ((==) `on` tvName)
                  (freeVariablesWellScoped [meth_ty]) all_cls_tvbs

    -- Explicitly quantify any kind variables bound by the class, if any.
    all_cls_tvbs :: [TyVarBndr]
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

maybeForallT :: [TyVarBndr] -> Cxt -> Type -> Type
maybeForallT tvbs cxt ty
  | null tvbs && null cxt        = ty
  | ForallT tvbs2 cxt2 ty2 <- ty = ForallT (tvbs ++ tvbs2) (cxt ++ cxt2) ty2
  | otherwise                    = ForallT tvbs cxt ty

data RecSelInfo
  = RecSelH98  Type -- The record field's type
  | RecSelGADT Type -- The record field's type
               Type -- The GADT return type

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
  (return . Map.lookup (ReifiableName name) =<< localFixityMap)
  (qReifyFixity name)

--------------------------------------
-- Reifying types
--------------------------------------
--
-- This section allows GHC <8.9 to call reifyFixity

#if __GLASGOW_HASKELL__ < 809
qReifyType :: forall m. Quasi m => Name -> m Type
qReifyType name = do
  info  <- qReify name
  cusks <- cusksEnabled
  case info_type info <|> info_kind cusks info of
    Just t  -> return t
    Nothing -> fail $ "Could not reify the full type of " ++ nameBase name
  where
    info_type :: Info -> Maybe Type
    info_type info =
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

    info_kind :: Bool -> Info -> Maybe Kind
    info_kind cusks info = do
      dec <- case info of
               ClassI d _  -> Just d
               TyConI d    -> Just d
               FamilyI d _ -> Just d
               _           -> Nothing
      Map.lookup (coerce name) $ filterTypes cusks [dec]

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
reifyTypeWithLocals_maybe name = qRecover
  (return . Map.lookup (ReifiableName name) =<< localTypeMap)
  (Just `fmap` qReifyType name)

-- | TODO RGS: Docs
filterTypes :: Bool -> [Dec] -> Map ReifiableName Type
filterTypes cusks decs =
  mk_reifiable_name_map $ concatMap filter_decs_with_types decs
  where
    standalone_type_map :: Map ReifiableName Type
    standalone_type_map = mk_reifiable_name_map $ mapMaybe filter_standalone_type decs

    -- Only contains Names of things with standalone type or kind signatures.
    filter_standalone_type :: Dec -> Maybe (Named Type)
    filter_standalone_type (SigD n ty)       = Just (n, ty)
#if __GLASGOW_HASKELL__ >= 802
    filter_standalone_type (PatSynSigD n ty) = Just (n, ty)
#endif
#if __GLASGOW_HASKELL__ >= 810
    filter_standalone_type (KiSigD n ki)     = Just (n, ki)
#endif
    filter_standalone_type _                 = Nothing

    filter_decs_with_types :: Dec -> [Named Type]
    filter_decs_with_types (FunD n _) =
      maybeToList $ lookup_standalone_type n
    filter_decs_with_types (ValD pat _ _) =
      mapMaybe lookup_standalone_type $ F.toList $ extractBoundNamesPat pat
    filter_decs_with_types (TySynD n tvbs rhs) =
      maybeToList $ lookup_standalone_kind n $ ty_syn_kind tvbs rhs
    filter_decs_with_types (ClassD _ n tvbs _ sub_decs) =
         maybeToList (lookup_standalone_kind n $ class_kind tvbs)
      ++ whenAlt assoc_type_cusks
                 (mapMaybe (class_assoc_type_kind cls_tvb_kind_map) sub_decs)
      ++ mapMaybe (class_meth_type n tvbs) sub_decs
      where
        m_cls_sak = Map.lookup (coerce n) standalone_type_map

        -- An associated type family can only have a CUSK if its parent class either:
        --
        -- 1. Has a standalone kind signature, or
        -- 2. Also has a CUSK (under -XCUSKs)
        assoc_type_cusks = isJust m_cls_sak || (cusks && all tvb_is_kinded tvbs)

        cls_tvb_kind_map
            -- If a class has a standalone kind signature, then we can determine the
            -- full kind of its associated types in 99% of cases.
            -- See Note [The limitations of standalone kind signatures] for what
            -- happens in the other 1% of cases.
          | Just ki <- m_cls_sak
          = let (arg_kis, _res_ki) = unravelType ki
                mb_vis_arg_kis     = map vis_arg_kind_maybe $ filterVisFunArgs arg_kis in
            Map.fromList [ (tvName tvb, tvb_kind)
                         | (tvb, mb_vis_arg_ki) <- zip tvbs mb_vis_arg_kis
                         , Just tvb_kind <- [mb_vis_arg_ki <|> tvb_kind_maybe tvb]
                         ]

          | otherwise
          = Map.fromList [ (tvName tvb, tvb_kind)
                         | tvb <- tvbs
                         , Just tvb_kind <- [tvb_kind_maybe tvb]
                         ]
    filter_decs_with_types (InstanceD
#if __GLASGOW_HASKELL__ >= 800
                                      _
#endif
                                      _ _ sub_decs) =
      concatMap filter_instance_sub_decs_with_types sub_decs
    filter_decs_with_types (ForeignD fgn) = [foreign_type fgn]
#if __GLASGOW_HASKELL__ >= 800
    filter_decs_with_types (DataD _ n tvbs m_ki cons _) =
         maybeToList (lookup_standalone_kind n $ datatype_kind tvbs m_ki)
      ++ concatMap (con_types n (map tvbToTANormalWithSig tvbs)) cons
    filter_decs_with_types (NewtypeD _ n tvbs m_ki con _) =
         maybeToList (lookup_standalone_kind n $ datatype_kind tvbs m_ki)
      ++ con_types n (map tvbToTANormalWithSig tvbs) con
    filter_decs_with_types (DataFamilyD n tvbs m_ki) =
      maybeToList $ lookup_standalone_kind n (open_ty_fam_kind tvbs m_ki)
    filter_decs_with_types (OpenTypeFamilyD (TypeFamilyHead n tvbs res_sig _)) =
      maybeToList $ lookup_standalone_kind n $ open_ty_fam_kind tvbs $ res_sig_to_kind res_sig
    filter_decs_with_types (ClosedTypeFamilyD (TypeFamilyHead n tvbs res_sig _) _) =
      maybeToList $ lookup_standalone_kind n $ closed_ty_fam_kind tvbs $ res_sig_to_kind res_sig
#else
    filter_decs_with_types (DataD _ n tvbs cons _) =
         maybeToList (lookup_standalone_kind n $ datatype_kind tvbs Nothing)
      ++ concatMap (con_types n (map tvbToTANormalWithSig tvbs)) cons
    filter_decs_with_types (NewtypeD _ n tvbs con _) =
         maybeToList (lookup_standalone_kind n $ datatype_kind tvbs Nothing)
      ++ con_types n (map tvbToTANormalWithSig tvbs) con
    filter_decs_with_types (FamilyD _ n tvbs m_ki) =
      maybeToList $ lookup_standalone_kind n $ open_ty_fam_kind tvbs m_ki
    filter_decs_with_types (ClosedTypeFamilyD n tvbs m_ki _) =
      maybeToList $ lookup_standalone_kind n $ closed_ty_fam_kind tvbs m_ki
#endif
#if __GLASGOW_HASKELL__ >= 808
    filter_decs_with_types (DataInstD _ _ lhs _ cons _)
      | (ConT n, ty_args) <- unfoldType lhs
      = concatMap (con_types n ty_args) cons
    filter_decs_with_types (NewtypeInstD _ _ lhs _ con _)
      | (ConT n, ty_args) <- unfoldType lhs
      = con_types n ty_args con
#else
    filter_decs_with_types (DataInstD _ n tys
#if __GLASGOW_HASKELL__ >= 800
                                      _
#endif
                                      cons _)
      = concatMap (con_types n (map TANormal tys)) cons
    filter_decs_with_types (NewtypeInstD _ n tys
#if __GLASGOW_HASKELL__ >= 800
                                         _
#endif
                                         con _)
      = con_types n (map TANormal tys) con
#endif
#if __GLASGOW_HASKELL__ >= 802
    filter_decs_with_types (PatSynD n _ _ _) =
      maybeToList $ lookup_standalone_type n
#endif
    filter_decs_with_types _ = []

    class_meth_type :: Name -> [TyVarBndr] -> Dec -> Maybe (Named Type)
    class_meth_type cls_name cls_tvbs sub_dec =
      case sub_dec of
        SigD meth_name meth_ty
          -> Just (meth_name, quantifyClassMethodType cls_name cls_tvbs True meth_ty)
        _ -> Nothing

    filter_instance_sub_decs_with_types :: Dec -> [Named Type]
    filter_instance_sub_decs_with_types d@DataInstD{}    = filter_decs_with_types d
    filter_instance_sub_decs_with_types d@NewtypeInstD{} = filter_decs_with_types d
    filter_instance_sub_decs_with_types _                = []

    foreign_type :: Foreign -> Named Type
    foreign_type (ImportF _ _ _ n ty) = (n, ty)
    foreign_type (ExportF _ _   n ty) = (n, ty)

    lookup_standalone_type :: Name -> Maybe (Named Type)
    lookup_standalone_type n = fmap (n,) $ Map.lookup (coerce n) standalone_type_map

    -- Used only for type-level declarations. If a standalone kind signature
    -- cannot be found, fall back on the declaration's CUSK (if applicable).
    lookup_standalone_kind :: Name -> Maybe Kind -> Maybe (Named Kind)
    lookup_standalone_kind n m_cusk =
      fmap (n,) $ Map.lookup (coerce n) standalone_type_map <|> whenAlt cusks m_cusk

    -- TODO RGS: Docs for the arguments
    con_types :: Name -> [TypeArg] -> Con -> [Named Type]
    con_types ty_name ty_args con =
         map (,full_con_ty) (conNames con)
      ++ map mk_rec_sel_type (rec_sel_infos con)
      where
        h98_tvbs   = freeVariablesWellScoped $ map probablyWrongUnTypeArg ty_args
        h98_res_ty = applyType (ConT ty_name) ty_args

        -- See Note [Use unSigType in filterTypes]
        full_con_ty = unSigType $ con_to_type h98_tvbs h98_res_ty con

        extract_rec_sel_info :: RecSelInfo -> ([TyVarBndr], Type, Type)
          -- Returns ( Selector type variable binders
          --         , Record field type
          --         , constructor result type )
        extract_rec_sel_info rec_sel_info =
          case rec_sel_info of
            RecSelH98 sel_ty -> (h98_tvbs, sel_ty, h98_res_ty)
            RecSelGADT sel_ty con_res_ty ->
              ( freeVariablesWellScoped [con_res_ty, sel_ty]
              , sel_ty, con_res_ty)

        mk_rec_sel_type :: Named RecSelInfo -> Named Type
        mk_rec_sel_type (n, rec_sel_info) =
          let (tvbs, sel_ty, con_res_ty) = extract_rec_sel_info rec_sel_info
              -- See Note [Use unSigType in filterTypes]
              full_sel_ty = unSigType $ maybeForallT tvbs [] $ mkArrows [con_res_ty] sel_ty
          in (n, full_sel_ty)

    -- TODO RGS: Docs for the arguments
    rec_sel_infos :: Con -> [Named RecSelInfo]
    rec_sel_infos NormalC{}                 = []
    rec_sel_infos InfixC{}                  = []
    rec_sel_infos (ForallC _ _ c)           = rec_sel_infos c
    rec_sel_infos (RecC _ vstys)            =
      map (\(n, _, sel_ty) -> (n, RecSelH98 sel_ty)) vstys
#if __GLASGOW_HASKELL__ >= 800
    rec_sel_infos GadtC{}                   = []
    rec_sel_infos (RecGadtC _ vstys ret_ty) =
      map (\(n, _, sel_ty) -> (n, RecSelGADT sel_ty ret_ty)) vstys
#endif

    -- Uncover the kind of an associated type family. There is an invariant
    -- that this function should only ever be called when the kind of the
    -- parent class is known (i.e., if it has a standalone kind signature or a
    -- CUSK). Despite this, it is possible for this function to return Nothing.
    -- See Note [The limitations of standalone kind signatures].
    class_assoc_type_kind :: Map Name Kind -> Dec -> Maybe (Named Kind)
    class_assoc_type_kind cls_tvb_kind_map sub_dec =
      case sub_dec of
#if __GLASGOW_HASKELL__ >= 800
        DataFamilyD n tf_tvbs m_ki ->
          fmap (n,) $ build_kind (map ascribe_tf_tvb_kind tf_tvbs) (default_res_ki m_ki)
        OpenTypeFamilyD (TypeFamilyHead n tf_tvbs res_sig _) ->
          fmap (n,) $ build_kind (map ascribe_tf_tvb_kind tf_tvbs)
                                 (default_res_ki $ res_sig_to_kind res_sig)
#else
        FamilyD _ n tf_tvbs m_ki ->
          fmap (n,) $ build_kind (map ascribe_tf_tvb_kind tf_tvbs) (default_res_ki m_ki)
#endif
        _ -> Nothing
      where
        ascribe_tf_tvb_kind :: TyVarBndr -> TyVarBndr
        ascribe_tf_tvb_kind tvb =
          case tvb of
            KindedTV{}  -> tvb
            PlainTV tvn -> KindedTV tvn $ fromMaybe StarT $ Map.lookup tvn cls_tvb_kind_map

-- If using GHC 8.10 or later, check if the -XCUSKs language extension is enabled.
-- If using an older GHC, return True, as the behavior of -XCUSKs was the norm.
cusksEnabled :: Quasi q => q Bool
cusksEnabled = do
#if __GLASGOW_HASKELL__ >= 810
  cusks <- qIsExtEnabled CUSKs
#else
  -- On earlier GHCs, the behavior of -XCUSKs was the norm.
  let cusks = True
#endif
  return cusks

-- Data types have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. All kind variables in the result kind are explicitly quantified.
datatype_kind :: [TyVarBndr] -> Maybe Kind -> Maybe Kind
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
class_kind :: [TyVarBndr] -> Maybe Kind
class_kind tvbs = whenAlt (all tvb_is_kinded tvbs) $
                  build_kind tvbs ConstraintT

-- Open type families and data families always have CUSKs. Type variables
-- without explicit kinds default to Type, as does the return kind if it
-- is not specified.
open_ty_fam_kind :: [TyVarBndr] -> Maybe Kind -> Maybe Kind
open_ty_fam_kind tvbs m_ki =
  build_kind (map default_tvb tvbs) (default_res_ki m_ki)

-- Closed type families have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. An explicit return kind is supplied.
closed_ty_fam_kind :: [TyVarBndr] -> Maybe Kind -> Maybe Kind
closed_ty_fam_kind tvbs m_ki =
  case m_ki of
    Just ki -> whenAlt (all tvb_is_kinded tvbs) $
               build_kind tvbs ki
    Nothing -> Nothing

-- Type synonyms have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. The right-hand-side type is annotated with an explicit kind.
ty_syn_kind :: [TyVarBndr] -> Type -> Maybe Kind
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
build_kind :: [TyVarBndr] -> Kind -> Maybe Kind
build_kind arg_kinds res_kind =
  fmap quantifyType $ fst $
  foldr go (Just res_kind, Set.fromList (freeVariables res_kind)) arg_kinds
  where
    go :: TyVarBndr -> (Maybe Kind, Set Name) -> (Maybe Kind, Set Name)
    go tvb (res, res_fvs) =
      case tvb of
        PlainTV n
          -> ( if n `Set.member` res_fvs
               then forall_vis tvb res
               else Nothing -- We have a type variable binder without an
                            -- explicit kind that is not used dependently, so
                            -- we cannot build a kind from it. This is the
                            -- only case where we return Nothing.
             , res_fvs
             )
        KindedTV n k
          -> ( if n `Set.member` res_fvs
               then forall_vis tvb res
               else fmap (ArrowT `AppT` k `AppT`) res
             , Set.fromList (freeVariables k) `Set.union` res_fvs
             )

    forall_vis :: TyVarBndr -> Maybe Kind -> Maybe Kind
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

tvb_is_kinded :: TyVarBndr -> Bool
tvb_is_kinded = isJust . tvb_kind_maybe

tvb_kind_maybe :: TyVarBndr -> Maybe Kind
tvb_kind_maybe PlainTV{}      = Nothing
tvb_kind_maybe (KindedTV _ k) = Just k

vis_arg_kind_maybe :: VisFunArg -> Maybe Kind
vis_arg_kind_maybe (VisFADep tvb) = tvb_kind_maybe tvb
vis_arg_kind_maybe (VisFAAnon k)  = Just k

default_tvb :: TyVarBndr -> TyVarBndr
default_tvb (PlainTV n)    = KindedTV n StarT
default_tvb tvb@KindedTV{} = tvb

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
      -- TODO RGS: This is a bit tricky, since we are using `Map.assocs localInfoMap`
      -- instead of `reifyWithLocals_maybe`. Explain why.
      all_infos <- fmap Map.assocs localInfoMap
      let name_infos = mapMaybe (\(ReifiableName n, i) ->
                                  if n `nameMatches` built_name
                                  then Just (n, i) else Nothing) all_infos
      return $ firstMatch (if ns then find_type_name
                                 else find_value_name) name_infos

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
