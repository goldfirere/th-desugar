{- Language/Haskell/TH/Desugar/Reify.hs

(c) Richard Eisenberg 2014
rae@cs.brynmawr.edu

Allows for reification from a list of declarations, without looking a name
up in the environment.
-}

{-# LANGUAGE CPP, GeneralizedNewtypeDeriving #-}

module Language.Haskell.TH.Desugar.Reify (
  -- * Reification
  reifyWithLocals_maybe, reifyWithLocals, reifyWithWarning, reifyInDecs,

  -- ** Fixity reification
  qReifyFixity, reifyFixity, reifyFixityWithLocals, reifyFixityInDecs,

  -- * Datatype lookup
  getDataD, dataConNameToCon, dataConNameToDataName,

  -- * Value and type lookup
  lookupValueNameWithLocals, lookupTypeNameWithLocals,
  mkDataNameWithLocals, mkTypeNameWithLocals,

  -- * Monad support
  DsMonad(..), DsM, withLocalDeclarations
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.RWS
import Data.List
import Data.Maybe
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import qualified Data.Set as S
#if __GLASGOW_HASKELL__ >= 800
import qualified Control.Monad.Fail as Fail
#else
import qualified Control.Monad as Fail
#endif

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
reifyWithWarning :: Quasi q => Name -> q Info
reifyWithWarning name = qRecover (reifyFail name) (qReify name)

-- | Print out a warning about separating splices and fail.
#if __GLASGOW_HASKELL__ >= 800
reifyFail :: Fail.MonadFail m => Name -> m a
#else
reifyFail :: Monad m => Name -> m a
#endif
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
#if __GLASGOW_HASKELL__ > 710
    DataD _cxt _name tvbs _mk cons _derivings -> return (tvbs, cons)
    NewtypeD _cxt _name tvbs _mk con _derivings -> return (tvbs, [con])
#else
    DataD _cxt _name tvbs cons _derivings -> return (tvbs, cons)
    NewtypeD _cxt _name tvbs con _derivings -> return (tvbs, [con])
#endif
    _ -> badDeclaration
  where badDeclaration =
          fail $ "The name (" ++ (show name) ++ ") refers to something " ++
                 "other than a datatype. " ++ err

-- | From the name of a data constructor, retrive the datatype definition it
-- is a part of.
dataConNameToDataName :: Quasi q => Name -> q Name
dataConNameToDataName con_name = do
  info <- reifyWithWarning con_name
  case info of
#if __GLASGOW_HASKELL__ > 710
    DataConI _name _type parent_name -> return parent_name
#else
    DataConI _name _type parent_name _fixity -> return parent_name
#endif
    _ -> fail $ "The name " ++ show con_name ++ " does not appear to be " ++
                "a data constructor."

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: Quasi q => Name -> q Con
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
class Quasi m => DsMonad m where
  -- | Produce a list of local declarations.
  localDeclarations :: m [Dec]

instance DsMonad Q where
  localDeclarations = return []
instance DsMonad IO where
  localDeclarations = return []

-- | A convenient implementation of the 'DsMonad' class. Use by calling
-- 'withLocalDeclarations'.
newtype DsM q a = DsM (ReaderT [Dec] q a)
  deriving ( Functor, Applicative, Monad, MonadTrans, Quasi
#if __GLASGOW_HASKELL__ >= 800
           , Fail.MonadFail
#endif
           )

instance Quasi q => DsMonad (DsM q) where
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
    match_fixity (InfixD fixity n') | n `nameMatches` n' = Just fixity
    match_fixity _                                       = Nothing

-- | A reified thing along with the name of that thing.
type Named a = (Name, a)

reifyInDec :: Name -> [Dec] -> Dec -> Maybe (Named Info)
reifyInDec n decs (FunD n' _) | n `nameMatches` n' = Just (n', mkVarI n decs)
reifyInDec n decs (ValD pat _ _)
  | Just n' <- find (nameMatches n) (S.elems (extractBoundNamesPat pat)) = Just (n', mkVarI n decs)
#if __GLASGOW_HASKELL__ > 710
reifyInDec n _    dec@(DataD    _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(NewtypeD _ n' _ _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
#else
reifyInDec n _    dec@(DataD    _ n' _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n _    dec@(NewtypeD _ n' _ _ _) | n `nameMatches` n' = Just (n', TyConI dec)
#endif
reifyInDec n _    dec@(TySynD n' _ _)       | n `nameMatches` n' = Just (n', TyConI dec)
reifyInDec n decs dec@(ClassD _ n' _ _ _)   | n `nameMatches` n'
  = Just (n', ClassI (stripClassDec dec) (findInstances n decs))
reifyInDec n decs (ForeignD (ImportF _ _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n decs ty)
reifyInDec n decs (ForeignD (ExportF _ _ n' ty)) | n `nameMatches` n'
  = Just (n', mkVarITy n decs ty)
#if __GLASGOW_HASKELL__ > 710
reifyInDec n decs dec@(OpenTypeFamilyD (TypeFamilyHead n' _ _ _)) | n `nameMatches` n'
  = Just (n', FamilyI (handleBug8884 dec) (findInstances n decs))
reifyInDec n decs dec@(DataFamilyD n' _ _) | n `nameMatches` n'
  = Just (n', FamilyI (handleBug8884 dec) (findInstances n decs))
reifyInDec n _    dec@(ClosedTypeFamilyD (TypeFamilyHead n' _ _ _) _) | n `nameMatches` n'
  = Just (n', FamilyI dec [])
#else
reifyInDec n decs dec@(FamilyD _ n' _ _) | n `nameMatches` n'
  = Just (n', FamilyI (handleBug8884 dec) (findInstances n decs))
#if __GLASGOW_HASKELL__ >= 707
reifyInDec n _    dec@(ClosedTypeFamilyD n' _ _ _) | n `nameMatches` n'
  = Just (n', FamilyI dec [])
#endif
#endif
#if __GLASGOW_HASKELL__ >= 801
reifyInDec n decs (PatSynD n' _ _ _) | n `nameMatches` n'
  = Just (n', mkPatSynI n decs)
#endif

#if __GLASGOW_HASKELL__ > 710
reifyInDec n decs (DataD _ ty_name tvbs _mk cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs _mk con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) [con]
  = Just info
#else
reifyInDec n decs (DataD _ ty_name tvbs cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) [con]
  = Just info
#endif
#if __GLASGOW_HASKELL__ > 710
reifyInDec n _decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just (n', ty) <- findType n sub_decs
  = Just (n', ClassOpI n (addClassCxt ty_name tvbs ty) ty_name)
#else
reifyInDec n decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just (n', ty) <- findType n sub_decs
  = Just (n', ClassOpI n (addClassCxt ty_name tvbs ty)
                       ty_name (fromMaybe defaultFixity $
                                reifyFixityInDecs n $ sub_decs ++ decs))
#endif
reifyInDec n decs (ClassD _ _ _ _ sub_decs)
  | Just info <- firstMatch (reifyInDec n (sub_decs ++ decs)) sub_decs
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
#if __GLASGOW_HASKELL__ > 710
reifyInDec n decs (DataInstD _ ty_name tys _ cons _)
  | Just info <- maybeReifyCon n decs ty_name tys cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys _ con _)
  | Just info <- maybeReifyCon n decs ty_name tys [con]
  = Just info
#else
reifyInDec n decs (DataInstD _ ty_name tys cons _)
  | Just info <- maybeReifyCon n decs ty_name tys cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys con _)
  | Just info <- maybeReifyCon n decs ty_name tys [con]
  = Just info
#endif

reifyInDec _ _ _ = Nothing

maybeReifyCon :: Name -> [Dec] -> Name -> [Type] -> [Con] -> Maybe (Named Info)
#if __GLASGOW_HASKELL__ > 710
maybeReifyCon n _decs ty_name ty_args cons
  | Just (n', con) <- findCon n cons
  = Just (n', DataConI n (maybeForallT tvbs [] $ con_to_type con) ty_name)
#else
maybeReifyCon n decs ty_name ty_args cons
  | Just (n', con) <- findCon n cons
  = Just (n', DataConI n (maybeForallT tvbs [] $ con_to_type con)
                         ty_name fixity)
#endif

  | Just (n', ty) <- findRecSelector n cons
      -- we don't try to ferret out naughty record selectors.
#if __GLASGOW_HASKELL__ > 710
  = Just (n', VarI n (maybeForallT tvbs [] $ mkArrows [result_ty] ty) Nothing)
#else
  = Just (n', VarI n (maybeForallT tvbs [] $ mkArrows [result_ty] ty) Nothing fixity)
#endif
  where
    result_ty = foldl AppT (ConT ty_name) ty_args

    con_to_type (NormalC _ stys) = mkArrows (map snd    stys)  result_ty
    con_to_type (RecC _ vstys)   = mkArrows (map thdOf3 vstys) result_ty
    con_to_type (InfixC t1 _ t2) = mkArrows (map snd [t1, t2]) result_ty
    con_to_type (ForallC bndrs cxt c) = ForallT bndrs cxt (con_to_type c)
#if __GLASGOW_HASKELL__ > 710
    con_to_type (GadtC _ stys rty)     = mkArrows (map snd    stys)  rty
    con_to_type (RecGadtC _ vstys rty) = mkArrows (map thdOf3 vstys) rty
#endif
#if __GLASGOW_HASKELL__ < 711
    fixity = fromMaybe defaultFixity $ reifyFixityInDecs n decs
#endif
    tvbs = map PlainTV $ S.elems $ freeNamesOfTypes ty_args
maybeReifyCon _ _ _ _ _ = Nothing

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
#if __GLASGOW_HASKELL__ > 710
    match_instance d@(DataInstD _ n' _ _ _ _)    | n `nameMatches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _ _) | n `nameMatches` n' = [d]
#else
    match_instance d@(DataInstD _ n' _ _ _)    | n `nameMatches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _) | n `nameMatches` n' = [d]
#endif
#if __GLASGOW_HASKELL__ >= 707
    match_instance d@(TySynInstD n' _)         | n `nameMatches` n' = [d]
#else
    match_instance d@(TySynInstD n' _ _)       | n `nameMatches` n' = [d]
#endif

#if __GLASGOW_HASKELL__ >= 711
    match_instance (InstanceD _ _ _ decs)
#else
    match_instance (InstanceD _ _ decs)
#endif
                                        = concatMap match_instance decs
    match_instance _                    = []

    ty_head (ForallT _ _ ty) = ty_head ty
    ty_head (AppT ty _)      = ty_head ty
    ty_head (SigT ty _)      = ty_head ty
    ty_head ty               = ty

stripClassDec :: Dec -> Dec
stripClassDec (ClassD cxt name tvbs fds sub_decs)
  = ClassD cxt name tvbs fds sub_decs'
  where
    sub_decs' = mapMaybe go sub_decs
    go (SigD n ty) = Just $ SigD n $ addClassCxt name tvbs ty
#if __GLASGOW_HASKELL__ > 710
    go d@(OpenTypeFamilyD {}) = Just d
    go d@(DataFamilyD {})     = Just d
#endif
    go _           = Nothing
stripClassDec dec = dec

addClassCxt :: Name -> [TyVarBndr] -> Type -> Type
addClassCxt class_name tvbs ty = ForallT tvbs class_cxt ty
  where
#if __GLASGOW_HASKELL__ < 709
    class_cxt = [ClassP class_name (map tvbToType tvbs)]
#else
    class_cxt = [foldl AppT (ConT class_name) (map tvbToType tvbs)]
#endif

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

findRecSelector :: Name -> [Con] -> Maybe (Named Type)
findRecSelector n = firstMatch match_con
  where
    match_con (RecC _ vstys)       = firstMatch match_rec_sel vstys
#if __GLASGOW_HASKELL__ >= 800
    match_con (RecGadtC _ vstys _) = firstMatch match_rec_sel vstys
#endif
    match_con (ForallC _ _ c)      = match_con c
    match_con _                    = Nothing

    match_rec_sel (n', _, ty) | n `nameMatches` n' = Just (n', ty)
    match_rec_sel _                                = Nothing

handleBug8884 :: Dec -> Dec
#if __GLASGOW_HASKELL__ >= 707
handleBug8884 = id
#else
handleBug8884 (FamilyD flav name tvbs m_kind)
  = FamilyD flav name tvbs (Just stupid_kind)
  where
    kind_from_maybe = fromMaybe StarT
    tvb_kind (PlainTV _)    = Nothing
    tvb_kind (KindedTV _ k) = Just k

    result_kind = kind_from_maybe m_kind
    args_kinds  = map (kind_from_maybe . tvb_kind) tvbs

    stupid_kind = mkArrows args_kinds result_kind
handleBug8884 dec = dec
#endif

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

-- | Like 'reifyWithLocals_maybe', but for fixities. Note that a return of
-- @Nothing@ might mean that the name is not in scope, or it might mean
-- that the name has no assigned fixity. (Use 'reifyWithLocals_maybe' if
-- you really need to tell the difference.)
reifyFixityWithLocals :: DsMonad q => Name -> q (Maybe Fixity)
reifyFixityWithLocals name = qRecover
  (return . reifyFixityInDecs name =<< localDeclarations)
  (qReifyFixity name)

--------------------------------------
-- Lookuping name value and type names
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
      case info of
        ClassI{}     -> Just n
        TyConI{}     -> Just n
        FamilyI{}    -> Just n
        PrimTyConI{} -> Just n
        TyVarI{}     -> Just n
        _            -> Nothing

    find_value_name (n, info) =
      case info of
        ClassOpI{} -> Just n
        DataConI{} -> Just n
        VarI{}     -> Just n
#if __GLASGOW_HASKELL__ >= 801
        PatSynI{}  -> Just n
#endif
        _          -> Nothing

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
