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
import Data.Function (on)
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set)

import Language.Haskell.TH.Datatype ( freeVariables, freeVariablesWellScoped
                                    , quantifyType, resolveTypeSynonyms )
import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax hiding ( lift )

import Language.Haskell.TH.Desugar.Util as Util

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

-- | Extract the 'DataFlavor', 'TyVarBndr's and constructors given the 'Name'
-- of a type.
getDataD :: DsMonad q
         => String       -- ^ Print this out on failure
         -> Name         -- ^ Name of the datatype (@data@ or @newtype@) of interest
         -> q (DataFlavor, [TyVarBndrVis], [Con])
getDataD err name = do
  info <- reifyWithLocals name
  dec <- case info of
           TyConI dec -> return dec
           _ -> badDeclaration
  case dec of
    DataD _cxt _name tvbs mk cons _derivings -> go Data tvbs mk cons
    NewtypeD _cxt _name tvbs mk con _derivings -> go Newtype tvbs mk [con]
#if __GLASGOW_HASKELL__ >= 906
    TypeDataD _name tvbs mk cons -> go Util.TypeData tvbs mk cons
#endif
    _ -> badDeclaration
  where
    go df tvbs mk cons = do
      let k = fromMaybe (ConT typeKindName) mk
      extra_tvbs <- mkExtraKindBinders k
      let all_tvbs = tvbs ++ extra_tvbs
      return (df, all_tvbs, cons)

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
mkExtraKindBinders :: forall q. Quasi q => Kind -> q [TyVarBndrVis]
mkExtraKindBinders k = do
  k' <- runQ $ resolveTypeSynonyms k
  let (fun_args, _) = unravelType k'
      vis_fun_args  = filterVisFunArgs fun_args
  mapM mk_tvb vis_fun_args
  where
    mk_tvb :: VisFunArg -> q TyVarBndrVis
    mk_tvb (VisFADep tvb) = return $ mapTVFlag (const BndrReq) tvb
    mk_tvb (VisFAAnon ki) = do
      name <- qNewName "a"
      pure $ kindedTVFlag name BndrReq ki

-- | From the name of a data constructor, retrive the datatype definition it
-- is a part of.
dataConNameToDataName :: DsMonad q => Name -> q Name
dataConNameToDataName con_name = do
  info <- reifyWithLocals con_name
  case info of
    DataConI _name _type parent_name -> return parent_name
    _ -> fail $ "The name " ++ show con_name ++ " does not appear to be " ++
                "a data constructor."

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: DsMonad q => Name -> q Con
dataConNameToCon con_name = do
  -- we need to get the field ordering from the constructor. We must reify
  -- the constructor to get the tycon, and then reify the tycon to get the `Con`s
  type_name <- dataConNameToDataName con_name
  (_, _, cons) <- getDataD "This seems to be an error in GHC." type_name
  let m_con = List.find (any (con_name ==) . get_con_name) cons
  case m_con of
    Just con -> return con
    Nothing -> impossible "Datatype does not contain one of its own constructors."

  where
    get_con_name (NormalC name _)     = [name]
    get_con_name (RecC name _)        = [name]
    get_con_name (InfixC _ name _)    = [name]
    get_con_name (ForallC _ _ con)    = get_con_name con
    get_con_name (GadtC names _ _)    = names
    get_con_name (RecGadtC names _ _) = names

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
  | Just n' <- List.find (nameMatches n) (F.toList (extractBoundNamesPat pat))
  = Just (n', mkVarI n decs)
reifyInDec n _    dec@(DataD    _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(NewtypeD _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(TySynD n' _ _)       | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n decs dec@(ClassD _ n' _ _ _)   | n `nameMatches` n'
  = Just (n', ClassI (quantifyClassDecMethods dec) (findInstances n decs))
reifyInDec n _    (ForeignD (ImportF _ _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n ty)
reifyInDec n _    (ForeignD (ExportF _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n ty)
reifyInDec n decs dec@(OpenTypeFamilyD (TypeFamilyHead n' _ _ _)) | n `nameMatches` n'
  = Just (n', FamilyI dec (findInstances n decs))
reifyInDec n decs dec@(DataFamilyD n' _ _) | n `nameMatches` n'
  = Just (n', FamilyI dec (findInstances n decs))
reifyInDec n _    dec@(ClosedTypeFamilyD (TypeFamilyHead n' _ _ _) _) | n `nameMatches` n'
  = Just (n', FamilyI dec [])
#if __GLASGOW_HASKELL__ >= 801
reifyInDec n decs (PatSynD n' _ _ _) | n `nameMatches` n'
  = Just (n', mkPatSynI n decs)
#endif
#if __GLASGOW_HASKELL__ >= 906
reifyInDec n _ dec@(TypeDataD n' _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
#endif

reifyInDec n decs (DataD _ ty_name tvbs _mk cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs _mk con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) [con]
  = Just info
reifyInDec n _decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just (n', ty) <- findType n sub_decs
  = Just (n', ClassOpI n (quantifyClassMethodType ty_name tvbs True ty) ty_name)
reifyInDec n decs (ClassD _ _ _ _ sub_decs)
  | Just info <- firstMatch (reifyInDec n decs) sub_decs
                 -- Important: don't pass (sub_decs ++ decs) to reifyInDec
                 -- above, or else type family defaults can be confused for
                 -- actual instances. See #134.
  = Just info
reifyInDec n decs (InstanceD _ _ _ sub_decs)
  | Just info <- firstMatch reify_in_instance sub_decs
  = Just info
  where
    reify_in_instance dec@(DataInstD {})    = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance dec@(NewtypeInstD {}) = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance _                     = Nothing
#if __GLASGOW_HASKELL__ >= 801
reifyInDec n decs (PatSynD pat_syn_name args _ _)
  | Just (n', full_sel_ty) <- maybeReifyPatSynRecSelector n decs pat_syn_name args
  = Just (n', VarI n full_sel_ty Nothing)
#endif
#if __GLASGOW_HASKELL__ >= 807
reifyInDec n decs (DataInstD _ _ lhs _ cons _)
  | (ConT ty_name, tys) <- unfoldType lhs
  , Just info <- maybeReifyCon n decs ty_name tys cons
  = Just info
reifyInDec n decs (NewtypeInstD _ _ lhs _ con _)
  | (ConT ty_name, tys) <- unfoldType lhs
  , Just info <- maybeReifyCon n decs ty_name tys [con]
  = Just info
#else
reifyInDec n decs (DataInstD _ ty_name tys _ cons _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys _ con _)
  | Just info <- maybeReifyCon n decs ty_name (map TANormal tys) [con]
  = Just info
#endif
#if __GLASGOW_HASKELL__ >= 906
reifyInDec n decs (TypeDataD ty_name tvbs _mk cons)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToTANormalWithSig tvbs) cons
  = Just info
#endif

reifyInDec _ _ _ = Nothing

maybeReifyCon :: Name -> [Dec] -> Name -> [TypeArg] -> [Con] -> Maybe (Named Info)
maybeReifyCon n _decs ty_name ty_args cons
  | Just (n', con) <- findCon n cons
    -- See Note [Use unSigType in maybeReifyCon]
  , let full_con_ty = unSigType $ con_to_type h98_tvbs h98_res_ty con
  = Just (n', DataConI n full_con_ty ty_name)

  | Just (n', rec_sel_info) <- findRecSelector n cons
  , let (tvbs, sel_ty, con_res_ty) = extract_rec_sel_info rec_sel_info
        -- See Note [Use unSigType in maybeReifyCon]
        full_sel_ty = unSigType $ maybeForallT tvbs [] $ mkArrows [con_res_ty] sel_ty
      -- we don't try to ferret out naughty record selectors.
  = Just (n', VarI n full_sel_ty Nothing)
  where
    extract_rec_sel_info :: RecSelInfo -> ([TyVarBndrSpec], Type, Type)
      -- Returns ( Selector type variable binders
      --         , Record field type
      --         , constructor result type )
    extract_rec_sel_info rec_sel_info =
      case rec_sel_info of
        RecSelH98 sel_ty ->
          ( changeTVFlags SpecifiedSpec h98_tvbs
          , sel_ty
          , h98_res_ty
          )
        RecSelGADT mb_con_tvbs sel_ty con_res_ty ->
          let -- If the GADT constructor type signature explicitly quantifies
              -- its type variables, make sure to use that same order in the
              -- record selector's type.
              con_tvbs' =
                case mb_con_tvbs of
                  Just con_tvbs -> con_tvbs
                  Nothing ->
                    changeTVFlags SpecifiedSpec $
                    freeVariablesWellScoped [con_res_ty, sel_ty] in
          ( con_tvbs'
          , sel_ty
          , con_res_ty
          )

    h98_tvbs   = freeVariablesWellScoped $
                 map probablyWrongUnTypeArg ty_args
    h98_res_ty = applyType (ConT ty_name) ty_args

maybeReifyCon _ _ _ _ _ = Nothing

#if __GLASGOW_HASKELL__ >= 801
-- | Attempt to reify the type of a pattern synonym record selector @n@.
-- The algorithm for computing this type works as follows:
--
-- 1. Reify the type of the parent pattern synonym. Broadly speaking, this
--    will look something like:
--
--    @
--    pattern P :: forall <req_tvbs>. req_cxt =>
--                 forall <prov_tvbs>. prov_cxt =>
--                 arg_ty_1 -> ... -> arg_ty_k -> res
--    @
--
-- 2. Check if @P@ is a record pattern synonym. If it isn't a record pattern
--    synonym, return 'Nothing'. If it is a record pattern synonym, it will
--    have @k@ record selectors @sel_1@, ..., @sel_k@.
--
-- 3. Check if @n@ is equal to some @sel_i@. If it isn't equal to any of them,
--    return @Nothing@. If it is equal to some @sel_i@, then return 'Just'
--    @sel_i@ paired with the following type:
--
--    @
--    sel_i :: forall <req_tvbs>. req_cxt => res -> arg_ty_i
--    @
maybeReifyPatSynRecSelector ::
  Name -> [Dec] -> Name -> PatSynArgs -> Maybe (Named Type)
maybeReifyPatSynRecSelector n decs pat_syn_name pat_syn_args =
  case pat_syn_args of
    -- Part (2) in the Haddocks
    RecordPatSyn fld_names
      -> firstMatch match_pat_syn_rec_sel $
         zip fld_names pat_syn_ty_vis_args
    _ -> Nothing
  where
    -- Part (3) in the Haddocks
    match_pat_syn_rec_sel :: (Name, Type) -> Maybe (Named Type)
    match_pat_syn_rec_sel (n', field_ty)
      | n `nameMatches` n'
      = Just ( n'
             , -- See Note [Use unSigType in maybeReifyCon]
               unSigType $
               maybeForallT pat_syn_ty_tvbs pat_syn_ty_req_cxt $
               ArrowT `AppT` pat_syn_ty_res `AppT` field_ty
             )
    match_pat_syn_rec_sel _
      = Nothing

    -- The type of the pattern synonym to which this record selector belongs,
    -- as described in part (1) in the Haddocks.
    pat_syn_ty :: Type
    pat_syn_ty =
      case findPatSynType pat_syn_name decs of
        Just ty -> ty
        Nothing -> no_type n

    pat_syn_ty_args :: FunArgs
    pat_syn_ty_res :: Type
    (pat_syn_ty_args, pat_syn_ty_res) =
      unravelType pat_syn_ty

    -- Decompose a pattern synonym type into the constituent parts described in
    -- part (1) in the Haddocks. The Haddocks present an idealized form of
    -- pattern synonym type signature where the required and provided foralls
    -- and contexts are made explicit. In reality, some of these parts may be
    -- omitted, so we have to be careful to handle every combination of
    -- explicit and implicit parts.
    pat_syn_ty_tvbs :: [TyVarBndrSpec]
    pat_syn_ty_req_cxt :: Cxt
    pat_syn_ty_vis_args :: [Type]
    (pat_syn_ty_tvbs, pat_syn_ty_req_cxt, pat_syn_ty_vis_args) =
      case pat_syn_ty_args of
        -- Both the required foralls and context are explicit.
        --
        -- The provided foralls and context may be explicit or implicit, but it
        -- doesn't really matter, as the type of a pattern synonym record
        -- selector only cares about the required foralls and context.
        -- Similarly for all cases below this one.
        FAForalls (ForallInvis req_tvbs) (FACxt req_cxt args) ->
          ( req_tvbs
          , req_cxt
          , mapMaybe vis_arg_anon_maybe $ filterVisFunArgs args
          )

        -- Only the required foralls are explicit. We can assume that there is
        -- no required context due to the case above not matching.
        FAForalls (ForallInvis req_tvbs) args ->
          ( req_tvbs
          , []
          , mapMaybe vis_arg_anon_maybe $ filterVisFunArgs args
          )

        -- The required context is explicit, but the required foralls are
        -- implicit. As a result, the order of type variables in the outer
        -- forall in the type of the pattern synonym is determined by the usual
        -- left-to-right scoped sort.
        --
        -- Note that there may be explicit, provided foralls in this case. For
        -- example, consider this example:
        --
        -- @
        -- data T a where
        --   MkT :: b -> T (Maybe b)
        --
        -- pattern X :: Show a => forall b. (a ~ Maybe b) => b -> T a
        -- pattern X{unX} = MkT unX
        -- @
        --
        -- You might worry that the type of @unX@ would need to mention @b@.
        -- But actually, you can't use @unX@ as a top-level record selector in
        -- the first place! If you try to do so, GHC will throw the following
        -- error:
        --
        -- @
        -- Cannot use record selector `unX' as a function due to escaped type variables
        -- @
        --
        -- As a result, we choose not to care about this corner case. We could
        -- imagine trying to detect this sort of thing here and throwing a
        -- similar error message, but detecting which type variables do or do
        -- not escape is tricky in general. (See the Haddocks for
        -- getRecordSelectors in L.H.TH.Desugar for more on this point.) As a
        -- result, we don't even bother trying. Similarly for the case below.
        FACxt req_cxt args ->
          ( changeTVFlags SpecifiedSpec $
            freeVariablesWellScoped [pat_syn_ty]
          , req_cxt
          , mapMaybe vis_arg_anon_maybe $ filterVisFunArgs args
          )

        -- The required foralls are implicit. We can assume that there is no
        -- required context due to the case above not matching.
        args ->
          ( changeTVFlags SpecifiedSpec $
            freeVariablesWellScoped [pat_syn_ty]
          , []
          , mapMaybe vis_arg_anon_maybe $ filterVisFunArgs args
          )

vis_arg_anon_maybe :: VisFunArg -> Maybe Type
vis_arg_anon_maybe (VisFAAnon ty) = Just ty
vis_arg_anon_maybe (VisFADep{})   = Nothing
#endif

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
                  | otherwise -> maybeForallT
                                   (changeTVFlags SpecifiedSpec h98_tvbs)
                                   [] ty
  where
    -- Note that we deliberately ignore linear types and use (->) everywhere.
    -- See [Gracefully handling linear types] in L.H.TH.Desugar.Core.
    go :: Con -> (Bool, Type) -- The Bool is True when dealing with a GADT
    go (NormalC _ stys)       = (False, mkArrows (map snd    stys)  h98_result_ty)
    go (RecC _ vstys)         = (False, mkArrows (map thdOf3 vstys) h98_result_ty)
    go (InfixC t1 _ t2)       = (False, mkArrows (map snd [t1, t2]) h98_result_ty)
    go (ForallC bndrs cxt c)  = liftSnd (ForallT bndrs cxt) (go c)
    go (GadtC _ stys rty)     = (True, mkArrows (map snd    stys)  rty)
    go (RecGadtC _ vstys rty) = (True, mkArrows (map thdOf3 vstys) rty)

mkVarI :: Name -> [Dec] -> Info
mkVarI n decs = mkVarITy n (maybe (no_type n) snd $ findType n decs)

mkVarITy :: Name -> Type -> Info
mkVarITy n ty = VarI n ty Nothing

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
    match_instance d@(InstanceD _ _ ty _)      | ConT n' <- ty_head ty
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
#else
    match_instance d@(DataInstD _ n' _ _ _ _)    | n `nameMatches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _ _) | n `nameMatches` n' = [d]
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

    match_instance (InstanceD _ _ _ decs)
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
    go d@(OpenTypeFamilyD {}) = Just d
    go d@(DataFamilyD {})     = Just d
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
  :: Name           -- ^ The class name.
  -> [TyVarBndrVis] -- ^ The class's type variable binders.
  -> Bool           -- ^ If 'True', prepend a class predicate.
  -> Type           -- ^ The method type.
  -> Type
quantifyClassMethodType cls_name cls_tvbs prepend meth_ty =
  add_cls_cxt quantified_meth_ty
  where
    add_cls_cxt :: Type -> Type
    add_cls_cxt
      | prepend   = ForallT (changeTVFlags SpecifiedSpec all_cls_tvbs) cls_cxt
      | otherwise = id

    cls_cxt :: Cxt
    cls_cxt = [foldl AppT (ConT cls_name) (map tvbToType cls_tvbs)]

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
                List.deleteFirstsBy ((==) `on` tvName)
                  (freeVariablesWellScoped [meth_ty]) all_cls_tvbs

    -- Explicitly quantify any kind variables bound by the class, if any.
    all_cls_tvbs :: [TyVarBndrUnit]
    all_cls_tvbs = freeVariablesWellScoped $ map tvbToTypeWithSig cls_tvbs

stripInstanceDec :: Dec -> Dec
stripInstanceDec (InstanceD over cxt ty _) = InstanceD over cxt ty []
stripInstanceDec dec                       = dec

mkArrows :: [Type] -> Type -> Type
mkArrows []     res_ty = res_ty
mkArrows (t:ts) res_ty = AppT (AppT ArrowT t) $ mkArrows ts res_ty

maybeForallT :: [TyVarBndrSpec] -> Cxt -> Type -> Type
maybeForallT tvbs cxt ty
  | null tvbs && null cxt        = ty
  | ForallT tvbs2 cxt2 ty2 <- ty = ForallT (tvbs ++ tvbs2) (cxt ++ cxt2) ty2
  | otherwise                    = ForallT tvbs cxt ty

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
        GadtC nms _ _    -> gadt_case con nms
        RecGadtC nms _ _ -> gadt_case con nms
        _                -> Nothing

    gadt_case :: Con -> [Name] -> Maybe (Named Con)
    gadt_case con nms = case List.find (n `nameMatches`) nms of
                          Just n' -> Just (n', con)
                          Nothing -> Nothing

data RecSelInfo
  = RecSelH98  Type -- The record field's type
  | RecSelGADT (Maybe [TyVarBndrSpec])
                    -- If the data constructor explicitly quantifies its type
                    -- variables with a forall, this will be Just. Otherwise,
                    -- this will be Nothing.
               Type -- The record field's type
               Type -- The GADT return type

findRecSelector :: Name -> [Con] -> Maybe (Named RecSelInfo)
findRecSelector n = firstMatch (match_con Nothing)
  where
    match_con :: Maybe [TyVarBndrSpec] -> Con -> Maybe (Named RecSelInfo)
    match_con mb_tvbs con =
      case con of
        RecC _ vstys ->
          fmap (liftSnd RecSelH98) $
          firstMatch match_rec_sel vstys
        RecGadtC _ vstys ret_ty ->
          fmap (liftSnd (\field_ty ->
            RecSelGADT (fmap (filter_ret_tvs ret_ty) mb_tvbs) field_ty ret_ty)) $
          firstMatch match_rec_sel vstys
        ForallC tvbs _ c ->
          -- This is the only recursive case, and it is also the place where
          -- the type variable binders are determined (hence the use of Just
          -- below). Note that GHC forbids nested foralls in GADT constructor
          -- type signatures, so it is guaranteed that if a type variable in
          -- the rest of the type signature appears free, then its binding site
          -- can be found in one of these binders found in this case.
          match_con (Just tvbs) c
        _ -> Nothing

    match_rec_sel (n', _, sel_ty)
      | n `nameMatches` n' = Just (n', sel_ty)
    match_rec_sel _        = Nothing

    -- There may be type variables in the type of a GADT constructor that do
    -- not appear in the type of a record selector. For example, consider:
    --
    --   data G a where
    --     MkG :: forall a b. { x :: a, y :: b } -> G a
    --
    -- The type of `x` will only quantify `a` and not `b`:
    --
    --   x :: forall a. G a -> a
    --
    -- Accordingly, we must filter out any type variables in the GADT
    -- constructor type that do not appear free in the return type. Note that
    -- this implies that we cannot support reifying the type of `y`, as `b`
    -- does not appear free in `G a`. This does not bother us, however, as we
    -- make no attempt to support naughty record selectors. (See the Haddocks
    -- for getRecordSelectors in L.H.TH.Desugar for more on this point.)
    --
    -- This mirrors the implementation of mkOneRecordSelector in GHC:
    -- https://gitlab.haskell.org/ghc/ghc/-/blob/37cfe3c0f4fb16189bbe3bb735f758cd6e3d9157/compiler/GHC/Tc/TyCl/Utils.hs#L908-909
    filter_ret_tvs :: Type -> [TyVarBndrSpec] -> [TyVarBndrSpec]
    filter_ret_tvs ret_ty =
      filter (\tvb -> tvName tvb `Set.member` ret_fvs)
      where
        ret_fvs = Set.fromList $ freeVariables [ret_ty]

---------------------------------
-- Reifying fixities
---------------------------------

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
    ClassOpI _ t _ -> Just t
    DataConI _ t _ -> Just t
    VarI _ t _     -> Just t
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
#if __GLASGOW_HASKELL__ >= 906
match_cusk n (TypeDataD n' tvbs m_ki _)
  | n `nameMatches` n'
  = datatype_kind tvbs m_ki
#endif
match_cusk _ _ = Nothing

-- Uncover the kind of an associated type family. There is an invariant
-- that this function should only ever be called when the kind of the
-- parent class is known (i.e., if it has a standalone kind signature or a
-- CUSK). Despite this, it is possible for this function to return Nothing.
-- See Note [The limitations of standalone kind signatures].
find_assoc_type_kind :: Name -> Map Name Kind -> Dec -> Maybe Kind
find_assoc_type_kind n cls_tvb_kind_map sub_dec =
  case sub_dec of
    DataFamilyD n' tf_tvbs m_ki
      |  n `nameMatches` n'
      -> build_kind (map ascribe_tf_tvb_kind tf_tvbs) (default_res_ki m_ki)
    OpenTypeFamilyD (TypeFamilyHead n' tf_tvbs res_sig _)
      |  n `nameMatches` n'
      -> build_kind (map ascribe_tf_tvb_kind tf_tvbs)
                    (default_res_ki $ res_sig_to_kind res_sig)
    _ -> Nothing
  where
    ascribe_tf_tvb_kind :: TyVarBndrVis -> TyVarBndrVis
    ascribe_tf_tvb_kind tvb =
      elimTVFlag
        (\tvn flag -> kindedTVFlag tvn flag $ fromMaybe StarT $ Map.lookup tvn cls_tvb_kind_map)
        (\_ _ _ -> tvb)
        tvb

-- Data types have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. All kind variables in the result kind are explicitly quantified.
datatype_kind :: [TyVarBndrVis] -> Maybe Kind -> Maybe Kind
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
class_kind :: [TyVarBndrVis] -> Maybe Kind
class_kind tvbs = whenAlt (all tvb_is_kinded tvbs) $
                  build_kind tvbs ConstraintT

-- Open type families and data families always have CUSKs. Type variables
-- without explicit kinds default to Type, as does the return kind if it
-- is not specified.
open_ty_fam_kind :: [TyVarBndrVis] -> Maybe Kind -> Maybe Kind
open_ty_fam_kind tvbs m_ki =
  build_kind (map default_tvb tvbs) (default_res_ki m_ki)

-- Closed type families have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. An explicit return kind is supplied.
closed_ty_fam_kind :: [TyVarBndrVis] -> Maybe Kind -> Maybe Kind
closed_ty_fam_kind tvbs m_ki =
  case m_ki of
    Just ki -> whenAlt (all tvb_is_kinded tvbs) $
               build_kind tvbs ki
    Nothing -> Nothing

-- Type synonyms have CUSKs when:
--
-- 1. All of their type variables have explicit kinds.
-- 2. The right-hand-side type is annotated with an explicit kind.
ty_syn_kind :: [TyVarBndrVis] -> Type -> Maybe Kind
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
build_kind :: [TyVarBndrVis] -> Kind -> Maybe Kind
build_kind arg_kinds res_kind =
  fmap quantifyType $ fst $
  foldr go (Just res_kind, Set.fromList (freeVariables res_kind)) arg_kinds
  where
    go :: TyVarBndrVis -> (Maybe Kind, Set Name) -> (Maybe Kind, Set Name)
    go tvb (res, res_fvs) =
      elimTV (\n ->
               ( if n `Set.member` res_fvs
                 then forall_ tvb res
                 else Nothing -- We have a type variable binder without an
                              -- explicit kind that is not used dependently, so
                              -- we cannot build a kind from it. This is the
                              -- only case where we return Nothing.
               , res_fvs
               ))
             (\n k ->
               ( if n `Set.member` res_fvs
                 then forall_ tvb res
                 else fmap (ArrowT `AppT` k `AppT`) res
               , Set.fromList (freeVariables k) `Set.union` res_fvs
               ))
             tvb

    forall_ :: TyVarBndrVis -> Maybe Kind -> Maybe Kind
#if __GLASGOW_HASKELL__ >= 809
    forall_ tvb m_ki = fmap forallT m_ki
      where
        bndrVis :: BndrVis
        bndrVis = elimTVFlag (\_ flag -> flag) (\_ flag _ -> flag) tvb
        forallT :: Kind -> Kind
        forallT = case bndrVis of
          BndrReq   -> ForallVisT (changeTVFlags () [tvb])
          BndrInvis -> ForallT (changeTVFlags SpecifiedSpec [tvb]) []
      -- One downside of this approach is that we generate kinds like this:
      --
      --   forall a -> forall b -> forall c -> (a, b, c)
      --
      -- Instead of this more compact kind:
      --
      --   forall a b c -> (a, b, c)
      --
      -- Thankfully, the difference is only cosmetic.
      --
      -- (TODO RGS: Revise these comments to mention forall a. forall b. ... instead
#else
    forall_ _   _    = Nothing
#endif

tvb_is_kinded :: TyVarBndr_ flag -> Bool
tvb_is_kinded = isJust . tvb_kind_maybe

tvb_kind_maybe :: TyVarBndr_ flag -> Maybe Kind
tvb_kind_maybe = elimTV (\_ -> Nothing) (\_ k -> Just k)

vis_arg_kind_maybe :: VisFunArg -> Maybe Kind
vis_arg_kind_maybe (VisFADep tvb) = tvb_kind_maybe tvb
vis_arg_kind_maybe (VisFAAnon k)  = Just k

default_tvb :: TyVarBndr_ flag -> TyVarBndr_ flag
default_tvb tvb = elimTVFlag (\n flag -> kindedTVFlag n flag StarT) (\_ _ _ -> tvb) tvb

default_res_ki :: Maybe Kind -> Kind
default_res_ki = fromMaybe StarT

res_sig_to_kind :: FamilyResultSig -> Maybe Kind
res_sig_to_kind NoSig          = Nothing
res_sig_to_kind (KindSig k)    = Just k
res_sig_to_kind (TyVarSig tvb) = tvb_kind_maybe tvb

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

lookupNameWithLocals :: forall q. DsMonad q => Bool -> String -> q (Maybe Name)
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
      firstMatchM (if ns then find_type_name
                         else find_value_name) infos

    -- These functions work over Named Infos so we can avoid performing
    -- tiresome pattern-matching to retrieve the name associated with each Info.
    find_type_name, find_value_name :: Named Info -> q (Maybe Name)
    find_type_name (n, info) = do
      name_space <- lookupInfoNameSpace info
      pure $ case name_space of
        TcClsName -> Just n
        VarName   -> Nothing
        DataName  -> Nothing

    find_value_name (n, info) = do
      name_space <- lookupInfoNameSpace info
      pure $ case name_space of
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
            traverse lookupInfoNameSpace mb_info

-- | Look up a name's 'NameSpace' from its 'Info'.
lookupInfoNameSpace :: DsMonad q => Info -> q NameSpace
lookupInfoNameSpace info =
  case info of
    ClassI{}     -> pure TcClsName
    TyConI{}     -> pure TcClsName
    FamilyI{}    -> pure TcClsName
    PrimTyConI{} -> pure TcClsName
    TyVarI{}     -> pure TcClsName

    ClassOpI{}   -> pure VarName
    VarI{}       -> pure VarName

    DataConI _dc_name _dc_ty parent_name -> do
      -- DataConI usually refers to a value-level Name, but it could also refer
      -- to a type-level 'Name' if the data constructor corresponds to a
      -- @type data@ declaration. In order to know for sure, we must perform
      -- some additional reification.
      mb_parent_info <- reifyWithLocals_maybe parent_name
      pure $ case mb_parent_info of
#if __GLASGOW_HASKELL__ >= 906
        Just (TyConI (TypeDataD {}))
          -> TcClsName
#endif
        _ -> DataName
#if __GLASGOW_HASKELL__ >= 801
    PatSynI{}    -> pure DataName
#endif
