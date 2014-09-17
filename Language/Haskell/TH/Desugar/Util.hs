{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Utility functions for th-desugar package.
-}

{-# LANGUAGE CPP, TupleSections #-}

module Language.Haskell.TH.Desugar.Util (
  reifyWithLocals, reifyWithWarning, newUniqueName,
  impossible, getDataD, dataConNameToCon,
  nameOccursIn, allNamesIn, mkTypeName, mkDataName,
  stripVarP_maybe, extractBoundNamesStmt, concatMapM,
  liftSndM, liftThdOf3M, stripPlainTV_maybe, dataConNameToDataName,
  liftSnd, liftThdOf3, splitAtList, extractBoundNamesDec,
  extractBoundNamesPat
  ) where

import Prelude hiding (mapM, foldl, concatMap, any)

import Language.Haskell.TH hiding ( cxt )
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.Monad

import qualified Data.Set as S
import Data.Foldable
import Data.Generics hiding ( Fixity )
import Data.Traversable
import Data.Monoid
import Data.Maybe

-- | Like @reify@ from Template Haskell, but looks also in any not-yet-typechecked
-- declarations. To establish this list of not-yet-typechecked declarations,
-- use 'withLocalDeclarations'. Returns 'Nothing' if reification fails.
-- Note that no inferred type information is available from local declarations;
-- bottoms may be used if necessary.
reifyWithLocals :: DsMonad q => Name -> q (Maybe Info)
reifyWithLocals name = qRecover
  (return . reifyInDecs name =<< localDeclarations)
  (Just `fmap` qReify name)

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

-- | Like newName, but even more unique (unique across different splices),
-- and with unique @nameBase@s.
newUniqueName :: Quasi q => String -> q Name
newUniqueName str = do
  n <- qNewName str
  qNewName $ show n

-- | Report that a certain TH construct is impossible
impossible :: Quasi q => String -> q a
impossible err = fail (err ++ "\n    This should not happen in Haskell.\n    Please email eir@cis.upenn.edu with your code if you see this.")

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

-- | From the name of a data constructor, retrive the datatype definition it
-- is a part of.
dataConNameToDataName :: Quasi q => Name -> q Name
dataConNameToDataName con_name = do
  info <- reifyWithWarning con_name
  case info of
    DataConI _name _type parent_name _fixity -> return parent_name
    _ -> fail $ "The name " ++ show con_name ++ " does not appear to be " ++
                "a data constructor."

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: Quasi q => Name -> q Con
dataConNameToCon con_name = do
  -- we need to get the field ordering from the constructor. We must reify
  -- the constructor to get the tycon, and then reify the tycon to get the `Con`s
  type_name <- dataConNameToDataName con_name
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

---------------------------
-- Reifying local declarations
---------------------------

firstMatch :: (a -> Maybe b) -> [a] -> Maybe b
firstMatch f xs = listToMaybe $ mapMaybe f xs

-- | Look through a list of declarations and possibly return a relevant 'Info'
reifyInDecs :: Name -> [Dec] -> Maybe Info
reifyInDecs n decs = firstMatch (reifyInDec n decs) decs

reifyInDec :: Name -> [Dec] -> Dec -> Maybe Info
reifyInDec n decs (FunD n' _) | n `matches` n' = Just $ mkVarI n decs
reifyInDec n decs (ValD pat _ _)
  | any (matches n) (S.elems (extractBoundNamesPat pat)) = Just $ mkVarI n decs
reifyInDec n _    dec@(DataD    _ n' _ _ _) | n `matches` n' = Just $ TyConI dec
reifyInDec n _    dec@(NewtypeD _ n' _ _ _) | n `matches` n' = Just $ TyConI dec
reifyInDec n _    dec@(TySynD n' _ _)       | n `matches` n' = Just $ TyConI dec
reifyInDec n decs dec@(ClassD _ n' _ _ _)   | n `matches` n'
  = Just $ ClassI (stripClassDec dec) (findInstances n decs)
reifyInDec n decs (ForeignD (ImportF _ _ _ n' ty)) | n `matches` n'
  = Just $ mkVarITy n decs ty
reifyInDec n decs (ForeignD (ExportF _ _ n' ty)) | n `matches` n'
  = Just $ mkVarITy n decs ty
reifyInDec n decs dec@(FamilyD _ n' _ _) | n `matches` n'
  = Just $ FamilyI dec (findInstances n decs)
#if __GLASGOW_HASKELL__ >= 707
reifyInDec n _    dec@(ClosedTypeFamilyD n' _ _ _) | n `matches` n'
  = Just $ FamilyI dec []
#endif

reifyInDec n decs (DataD _ ty_name tvbs cons _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) cons
  = Just info
reifyInDec n decs (NewtypeD _ ty_name tvbs con _)
  | Just info <- maybeReifyCon n decs ty_name (map tvbToType tvbs) [con]
  = Just info
reifyInDec n decs (ClassD _ _ _ _ sub_decs)
  | Just info <- firstMatch (reifyInDec n (sub_decs ++ decs)) sub_decs
  = Just info    -- must necessarily *not* be a method, because type signatures
                 -- don't reify
reifyInDec n decs (ClassD _ ty_name tvbs _ sub_decs)
  | Just ty <- findType n sub_decs
  = Just $ ClassOpI n (addClassCxt ty_name tvbs ty)
                    ty_name (findFixity n $ sub_decs ++ decs)
reifyInDec n decs (InstanceD _ _ sub_decs)
  | Just info <- firstMatch reify_in_instance sub_decs
  = Just info
  where
    reify_in_instance dec@(DataInstD {})    = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance dec@(NewtypeInstD {}) = reifyInDec n (sub_decs ++ decs) dec
    reify_in_instance _                     = Nothing
reifyInDec n decs (DataInstD _ ty_name tys cons _)
  | Just info <- maybeReifyCon n decs ty_name tys cons
  = Just info
reifyInDec n decs (NewtypeInstD _ ty_name tys con _)
  | Just info <- maybeReifyCon n decs ty_name tys [con]
  = Just info

reifyInDec _ _ _ = Nothing

maybeReifyCon :: Name -> [Dec] -> Name -> [Type] -> [Con] -> Maybe Info
maybeReifyCon n decs ty_name ty_args cons
  | Just con <- findCon n cons
  = Just $ DataConI n (maybeForallT tvbs [] $ con_to_type con)
                    ty_name fixity

  | Just ty <- findRecSelector n cons
      -- we don't try to ferret out naughty record selectors.
  = Just $ VarI n (maybeForallT tvbs [] $ mkArrows [result_ty] ty) Nothing fixity
  where
    result_ty = foldl AppT (ConT ty_name) ty_args

    con_to_type (NormalC _ stys) = mkArrows (map snd    stys)  result_ty
    con_to_type (RecC _ vstys)   = mkArrows (map thdOf3 vstys) result_ty
    con_to_type (InfixC t1 _ t2) = mkArrows (map snd [t1, t2]) result_ty
    con_to_type (ForallC bndrs cxt c) = ForallT bndrs cxt (con_to_type c)

    fixity = findFixity n decs
    tvbs = map PlainTV $ S.elems $ freeNamesOfTypes ty_args
maybeReifyCon _ _ _ _ _ = Nothing

mkVarI :: Name -> [Dec] -> Info
mkVarI n decs = mkVarITy n decs (fromMaybe no_type $ findType n decs)
  where
    no_type = error $ "No type information found in local declaration for "
                      ++ show n    

mkVarITy :: Name -> [Dec] -> Type -> Info
mkVarITy n decs ty = VarI n ty Nothing (findFixity n decs)
    
findFixity :: Name -> [Dec] -> Fixity
findFixity n = fromMaybe defaultFixity . firstMatch match_fixity
  where
    match_fixity (InfixD fixity n') | n `matches` n' = Just fixity
    match_fixity _                                   = Nothing

findType :: Name -> [Dec] -> Maybe Type
findType n = firstMatch match_type
  where
    match_type (SigD n' ty) | n `matches` n' = Just ty
    match_type _                             = Nothing

findInstances :: Name -> [Dec] -> [Dec]
findInstances n = map stripInstanceDec . concatMap match_instance
  where
    match_instance d@(InstanceD _ ty _)        | ConT n' <- ty_head ty
                                               , n `matches` n' = [d]
    match_instance d@(DataInstD _ n' _ _ _)    | n `matches` n' = [d]
    match_instance d@(NewtypeInstD _ n' _ _ _) | n `matches` n' = [d]
    match_instance d@(TySynInstD n' _)         | n `matches` n' = [d]
    match_instance (InstanceD _ _ decs) = concatMap match_instance decs
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
    go _           = Nothing
stripClassDec dec = dec

addClassCxt :: Name -> [TyVarBndr] -> Type -> Type
addClassCxt class_name tvbs ty = ForallT tvbs class_cxt ty
  where
#if __GLASGOW_HASKELL__ < 709
    class_cxt = [ClassP class_name (map (VarT . tvbName) tvbs)]
#else
    class_cxt = [applyTvbs ty_name tvbs]
#endif

stripInstanceDec :: Dec -> Dec
stripInstanceDec (InstanceD cxt ty _) = InstanceD cxt ty []
stripInstanceDec dec                  = dec

mkArrows :: [Type] -> Type -> Type
mkArrows []     res_ty = res_ty
mkArrows (t:ts) res_ty = AppT (AppT ArrowT t) $ mkArrows ts res_ty

maybeForallT :: [TyVarBndr] -> Cxt -> Type -> Type
maybeForallT tvbs cxt ty
  | null tvbs && null cxt        = ty
  | ForallT tvbs2 cxt2 ty2 <- ty = ForallT (tvbs ++ tvbs2) (cxt ++ cxt2) ty2
  | otherwise                    = ForallT tvbs cxt ty

findCon :: Name -> [Con] -> Maybe Con
findCon n = find match_con
  where
    match_con (NormalC n' _)  = n `matches` n'
    match_con (RecC n' _)     = n `matches` n'
    match_con (InfixC _ n' _) = n `matches` n'
    match_con (ForallC _ _ c) = match_con c

findRecSelector :: Name -> [Con] -> Maybe Type
findRecSelector n = firstMatch match_con
  where
    match_con (RecC _ vstys)  = firstMatch match_rec_sel vstys
    match_con (ForallC _ _ c) = match_con c
    match_con _               = Nothing

    match_rec_sel (n', _, ty) | n `matches` n' = Just ty
    match_rec_sel _                     = Nothing
    

tvbName :: TyVarBndr -> Name
tvbName (PlainTV n)    = n
tvbName (KindedTV n _) = n

tvbToType :: TyVarBndr -> Type
tvbToType = VarT . tvbName

thdOf3 :: (a,b,c) -> c
thdOf3 (_,_,c) = c

freeNamesOfTypes :: [Type] -> S.Set Name
freeNamesOfTypes = mconcat . map go
  where
    go (ForallT tvbs cxt ty) = (go ty <> mconcat (map go_pred cxt))
                               S.\\ S.fromList (map tvbName tvbs)
    go (AppT t1 t2)          = go t1 <> go t2
    go (SigT ty _)           = go ty
    go (VarT n)              = S.singleton n
    go _                     = S.empty

#if __GLASGOW_HASKELL__ > 709
    go_pred = go
#else
    go_pred (ClassP _ tys) = freeNamesOfTypes tys
    go_pred (EqualP t1 t2) = go t1 <> go t2
#endif

matches :: Name -> Name -> Bool
matches n1@(Name occ1 flav1) n2@(Name occ2 flav2)
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
    
