{- Language/Haskell/TH/Desugar/Core.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Desugars full Template Haskell syntax into a smaller core syntax for further
processing. The desugared types and constructors are prefixed with a D.
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, CPP, DeriveDataTypeable #-}

module Language.Haskell.TH.Desugar.Core where

import Prelude hiding (mapM, foldl, foldr, all, elem, exp, concatMap, and)

import Language.Haskell.TH hiding (match, clause, cxt)
import Language.Haskell.TH.Syntax hiding (lift)

import Control.Applicative
import Control.Monad hiding (mapM)
import Control.Monad.Zip
import Control.Monad.Writer hiding (mapM)
import Data.Foldable
import Data.Traversable
import Data.Data hiding (Fixity)

import qualified Data.Set as S
import GHC.Exts

import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Reify

-- | Corresponds to TH's @Exp@ type. Note that @DLamE@ takes names, not patterns.
data DExp = DVarE Name
          | DConE Name
          | DLitE Lit
          | DAppE DExp DExp
          | DLamE [Name] DExp
          | DCaseE DExp [DMatch]
          | DLetE [DLetDec] DExp
          | DSigE DExp DType
          deriving (Show, Typeable, Data)


-- | Corresponds to TH's @Pat@ type.
data DPat = DLitPa Lit
          | DVarPa Name
          | DConPa Name [DPat]
          | DTildePa DPat
          | DBangPa DPat
          | DWildPa
          deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Type@ type.
data DType = DForallT [DTyVarBndr] DCxt DType
           | DAppT DType DType
           | DSigT DType DKind
           | DVarT Name
           | DConT Name
           | DArrowT
           | DLitT TyLit
           deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Kind@ type, which is a synonym for @Type@. 'DKind', though,
--   only contains constructors that make sense for kinds.
data DKind = DForallK [Name] DKind
           | DVarK Name
           | DConK Name [DKind]
           | DArrowK DKind DKind
           | DStarK
           deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Cxt@
type DCxt = [DPred]

-- | Corresponds to TH's @Pred@
data DPred = DAppPr DPred DType
           | DSigPr DPred DKind
           | DVarPr Name
           | DConPr Name
           deriving (Show, Typeable, Data)

-- | Corresponds to TH's @TyVarBndr@. Note that @PlainTV x@ and @KindedTV x StarT@ are
--   distinct, so we retain that distinction here.
data DTyVarBndr = DPlainTV Name
                | DKindedTV Name DKind
                deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Match@ type.
data DMatch = DMatch DPat DExp
  deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Clause@ type.
data DClause = DClause [DPat] DExp
  deriving (Show, Typeable, Data)

-- | Declarations as used in a @let@ statement.
data DLetDec = DFunD Name [DClause]
             | DValD DPat DExp
             | DSigD Name DType
             | DInfixD Fixity Name
             deriving (Show, Typeable, Data)

-- | Is it a @newtype@ or a @data@ type?
data NewOrData = Newtype
               | Data
               deriving (Eq, Show, Typeable, Data)

-- | Corresponds to TH's @Dec@ type.
data DDec = DLetDec DLetDec
          | DDataD NewOrData DCxt Name [DTyVarBndr] [DCon] [Name]
          | DTySynD Name [DTyVarBndr] DType
          | DClassD DCxt Name [DTyVarBndr] [FunDep] [DDec]
          | DInstanceD DCxt DType [DDec]
          | DForeignD DForeign
          | DPragmaD DPragma
          | DFamilyD FamFlavour Name [DTyVarBndr] (Maybe DKind)
          | DDataInstD NewOrData DCxt Name [DType] [DCon] [Name]
          | DTySynInstD Name DTySynEqn
          | DClosedTypeFamilyD Name [DTyVarBndr] (Maybe DKind) [DTySynEqn]
          | DRoleAnnotD Name [Role]
          deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Con@ type.
data DCon = DCon [DTyVarBndr] DCxt Name DConFields
          deriving (Show, Typeable, Data)

-- | A list of fields either for a standard data constructor or a record
-- data constructor.
data DConFields = DNormalC [DStrictType]
                | DRecC [DVarStrictType]
                deriving (Show, Typeable, Data)

-- | Corresponds to TH's @StrictType@ type.
type DStrictType = (Strict, DType)

-- | Corresponds to TH's @VarStrictType@ type.
type DVarStrictType = (Name, Strict, DType)

-- | Corresponds to TH's @Foreign@ type.
data DForeign = DImportF Callconv Safety String Name DType
              | DExportF Callconv String Name DType
              deriving (Show, Typeable, Data)

-- | Corresponds to TH's @Pragma@ type.
data DPragma = DInlineP Name Inline RuleMatch Phases
             | DSpecialiseP Name DType (Maybe Inline) Phases
             | DSpecialiseInstP DType
             | DRuleP String [DRuleBndr] DExp DExp Phases
             | DAnnP AnnTarget DExp
             deriving (Show, Typeable, Data)

-- | Corresponds to TH's @RuleBndr@ type.
data DRuleBndr = DRuleVar Name
               | DTypedRuleVar Name DType
               deriving (Show, Typeable, Data)

-- | Corresponds to TH's @TySynEqn@ type (to store type family equations).
data DTySynEqn = DTySynEqn [DType] DType
               deriving (Show, Typeable, Data)

#if __GLASGOW_HASKELL__ < 707
-- | Same as @Role@ from TH; defined here for GHC 7.6.3 compatibility.
data Role = NominalR | RepresentationalR | PhantomR | InferR
          deriving (Show, Typeable, Data)

-- | Same as @AnnTarget@ from TH; defined here for GHC 7.6.3 compatibility.
data AnnTarget = ModuleAnnotation
               | TypeAnnotation Name
               | ValueAnnotation Name
               deriving (Show, Typeable, Data)
#endif

-- | Corresponds to TH's @Info@ type.
data DInfo = DTyConI DDec (Maybe [DInstanceDec])
           | DVarI Name DType (Maybe Name) Fixity
               -- ^ The @Maybe Name@ stores the name of the enclosing definition
               -- (datatype, for a data constructor; class, for a method),
               -- if any
           | DTyVarI Name DKind
           | DPrimTyConI Name Int Bool
               -- ^ The @Int@ is the arity; the @Bool@ is whether this tycon
               -- is unlifted.
           deriving (Show, Typeable, Data)

type DInstanceDec = DDec -- ^ Guaranteed to be an instance declaration

-- | Desugar an expression
dsExp :: DsMonad q => Exp -> q DExp
dsExp (VarE n) = return $ DVarE n
dsExp (ConE n) = return $ DConE n
dsExp (LitE lit) = return $ DLitE lit
dsExp (AppE e1 e2) = DAppE <$> dsExp e1 <*> dsExp e2
dsExp (InfixE Nothing op Nothing) = dsExp op
dsExp (InfixE (Just lhs) op Nothing) = DAppE <$> (dsExp op) <*> (dsExp lhs)
dsExp (InfixE Nothing op (Just rhs)) = do
  lhsName <- newUniqueName "lhs"
  op' <- dsExp op
  rhs' <- dsExp rhs
  return $ DLamE [lhsName] (foldl DAppE op' [DVarE lhsName, rhs'])
dsExp (InfixE (Just lhs) op (Just rhs)) =
  DAppE <$> (DAppE <$> dsExp op <*> dsExp lhs) <*> dsExp rhs
dsExp (UInfixE _ _ _) =
  fail "Cannot desugar unresolved infix operators."
dsExp (ParensE exp) = dsExp exp
dsExp (LamE pats exp) = dsLam pats =<< dsExp exp
dsExp (LamCaseE matches) = do
  x <- newUniqueName "x"
  matches' <- dsMatches x matches
  return $ DLamE [x] (DCaseE (DVarE x) matches')
dsExp (TupE exps) = do
  exps' <- mapM dsExp exps
  return $ foldl DAppE (DConE $ tupleDataName (length exps)) exps'
dsExp (UnboxedTupE exps) =
  foldl DAppE (DConE $ unboxedTupleDataName (length exps)) <$> mapM dsExp exps
dsExp (CondE e1 e2 e3) =
  dsExp (CaseE e1 [ Match (ConP 'True [])  (NormalB e2) []
                  , Match (ConP 'False []) (NormalB e3) [] ])
dsExp (MultiIfE guarded_exps) =
  let failure = DAppE (DVarE 'error) (DLitE (StringL "Non-exhaustive guards in multi-way if")) in
  dsGuards guarded_exps failure
dsExp (LetE decs exp) = DLetE <$> dsLetDecs decs <*> dsExp exp
dsExp (CaseE exp matches) = do
  scrutinee <- newUniqueName "scrutinee"
  exp' <- dsExp exp
  matches' <- dsMatches scrutinee matches
  return $ DLetE [DValD (DVarPa scrutinee) exp'] $
           DCaseE (DVarE scrutinee) matches'
dsExp (DoE stmts) = dsDoStmts stmts
dsExp (CompE stmts) = dsComp stmts
dsExp (ArithSeqE (FromR exp)) = DAppE (DVarE 'enumFrom) <$> dsExp exp
dsExp (ArithSeqE (FromThenR exp1 exp2)) =
  DAppE <$> (DAppE (DVarE 'enumFromThen) <$> dsExp exp1) <*> dsExp exp2
dsExp (ArithSeqE (FromToR exp1 exp2)) =
  DAppE <$> (DAppE (DVarE 'enumFromTo) <$> dsExp exp1) <*> dsExp exp2
dsExp (ArithSeqE (FromThenToR e1 e2 e3)) =
  DAppE <$> (DAppE <$> (DAppE (DVarE 'enumFromThenTo) <$> dsExp e1) <*>
                               dsExp e2) <*>
            dsExp e3
dsExp (ListE exps) = go exps
  where go [] = return $ DConE '[]
        go (h : t) = DAppE <$> (DAppE (DConE '(:)) <$> dsExp h) <*> go t
dsExp (SigE exp ty) = DSigE <$> dsExp exp <*> dsType ty
dsExp (RecConE con_name field_exps) = do
  con <- dataConNameToCon con_name
  reordered <- case con of
                 RecC _name fields -> reorderFields fields field_exps
                                                    (repeat $ DVarE 'undefined)
                 _ -> impossible $ "Record syntax used with non-record constructor "
                                   ++ (show con_name) ++ "."
  return $ foldl DAppE (DConE con_name) reordered
dsExp (RecUpdE exp field_exps) = do
  -- here, we need to use one of the field names to find the tycon, somewhat dodgily
  first_name <- case field_exps of
                  ((name, _) : _) -> return name
                  _ -> impossible "Record update with no fields listed."
  info <- reifyWithLocals first_name
  applied_type <- case info of
                    VarI _name ty _m_dec _fixity -> extract_first_arg ty
                    _ -> impossible "Record update with an invalid field name."
  type_name <- extract_type_name applied_type
  (_, cons) <- getDataD "This seems to be an error in GHC." type_name
  let filtered_cons = filter_cons_with_names cons (map fst field_exps)
  exp' <- dsExp exp
  matches <- mapM con_to_dmatch filtered_cons
  let all_matches
        | length filtered_cons == length cons = matches
        | otherwise                           = matches ++ [error_match]
  return $ DCaseE exp' all_matches
  where
    extract_first_arg :: DsMonad q => Type -> q Type
    extract_first_arg (AppT (AppT ArrowT arg) _) = return arg
    extract_first_arg (ForallT _ _ t) = extract_first_arg t
    extract_first_arg (SigT t _) = extract_first_arg t
    extract_first_arg _ = impossible "Record selector not a function."

    extract_type_name :: DsMonad q => Type -> q Name
    extract_type_name (AppT t1 _) = extract_type_name t1
    extract_type_name (SigT t _) = extract_type_name t
    extract_type_name (ConT n) = return n
    extract_type_name _ = impossible "Record selector domain not a datatype."
    
    filter_cons_with_names cons field_names =
      filter has_names cons
      where
        has_names (RecC _con_name args) =
          let con_field_names = map fst_of_3 args in
          all (`elem` con_field_names) field_names
        has_names (ForallC _ _ c) = has_names c
        has_names _               = False

    con_to_dmatch :: DsMonad q => Con -> q DMatch
    con_to_dmatch (RecC con_name args) = do
      let con_field_names = map fst_of_3 args
      field_var_names <- mapM (newUniqueName . nameBase) con_field_names
      DMatch (DConPa con_name (map DVarPa field_var_names)) <$>
             (foldl DAppE (DConE con_name) <$>
                    (reorderFields args field_exps (map DVarE field_var_names)))
    con_to_dmatch (ForallC _ _ c) = con_to_dmatch c
    con_to_dmatch _ = impossible "Internal error within th-desugar."

    error_match = DMatch DWildPa (DAppE (DVarE 'error)
                   (DLitE (StringL "Non-exhaustive patterns in record update")))

    fst_of_3 (x, _, _) = x

-- | Desugar a lambda expression, where the body has already been desugared
dsLam :: DsMonad q => [Pat] -> DExp -> q DExp
dsLam pats exp
  | Just names <- mapM stripVarP_maybe pats
  = return $ DLamE names exp
  | otherwise
  = do arg_names <- replicateM (length pats) (newUniqueName "arg")
       let scrutinee = mkTupleDExp (map DVarE arg_names)
       (pats', exp') <- dsPatsOverExp pats exp
       let match = DMatch (mkTupleDPat pats') exp'
       return $ DLamE arg_names (DCaseE scrutinee [match])

-- | Desugar a list of matches for a @case@ statement
dsMatches :: DsMonad q
          => Name     -- ^ Name of the scrutinee, which must be a bare var
          -> [Match]  -- ^ Matches of the @case@ statement
          -> q [DMatch]
dsMatches scr = go
  where
    go :: DsMonad q => [Match] -> q [DMatch]
    go [] = return []
    go (Match pat body where_decs : rest) = do
      rest' <- go rest
      let failure = DCaseE (DVarE scr) rest'  -- this might be an empty case.
      exp' <- dsBody body where_decs failure
      (pat', exp'') <- dsPatOverExp pat exp'
      uni_pattern <- isUniversalPattern pat' -- incomplete attempt at #6
      if uni_pattern
      then return [DMatch pat' exp'']
      else return (DMatch pat' exp'' : rest')

-- | Desugar a @Body@
dsBody :: DsMonad q
       => Body      -- ^ body to desugar
       -> [Dec]     -- ^ "where" declarations
       -> DExp      -- ^ what to do if the guards don't match
       -> q DExp
dsBody (NormalB exp) decs _ =
  maybeDLetE <$> dsLetDecs decs <*> dsExp exp
dsBody (GuardedB guarded_exps) decs failure =
  maybeDLetE <$> dsLetDecs decs <*> dsGuards guarded_exps failure

-- | If decs is non-empty, delcare them in a let:
maybeDLetE :: [DLetDec] -> DExp -> DExp
maybeDLetE [] exp   = exp
maybeDLetE decs exp = DLetE decs exp

-- | If matches is non-empty, make a case statement; otherwise make an error statement
maybeDCaseE :: String -> DExp -> [DMatch] -> DExp
maybeDCaseE err _     []      = DAppE (DVarE 'error) (DLitE (StringL err))
maybeDCaseE _   scrut matches = DCaseE scrut matches

-- | Desugar guarded expressions
dsGuards :: DsMonad q
         => [(Guard, Exp)]  -- ^ Guarded expressions
         -> DExp            -- ^ What to do if none of the guards match
         -> q DExp
dsGuards [] thing_inside = return thing_inside
dsGuards ((NormalG gd, exp) : rest) thing_inside =
  dsGuards ((PatG [NoBindS gd], exp) : rest) thing_inside
dsGuards ((PatG stmts, exp) : rest) thing_inside = do
  success <- dsExp exp
  failure <- dsGuards rest thing_inside
  dsGuardStmts stmts success failure

-- | Desugar the @Stmt@s in a guard
dsGuardStmts :: DsMonad q
             => [Stmt]  -- ^ The @Stmt@s to desugar
             -> DExp    -- ^ What to do if the @Stmt@s yield success
             -> DExp    -- ^ What to do if the @Stmt@s yield failure
             -> q DExp
dsGuardStmts [] success _failure = return success
dsGuardStmts (BindS pat exp : rest) success failure = do
  success' <- dsGuardStmts rest success failure
  (pat', success'') <- dsPatOverExp pat success'
  exp' <- dsExp exp
  return $ DCaseE exp' [DMatch pat' success'', DMatch DWildPa failure]
dsGuardStmts (LetS decs : rest) success failure = do
  decs' <- dsLetDecs decs
  success' <- dsGuardStmts rest success failure
  return $ DLetE decs' success'
  -- special-case a final pattern containing "otherwise" or "True"
  -- note that GHC does this special-casing, too, in DsGRHSs.isTrueLHsExpr
dsGuardStmts [NoBindS exp] success _failure
  | VarE name <- exp
  , name == 'otherwise
  = return success

  | ConE name <- exp
  , name == 'True
  = return success
dsGuardStmts (NoBindS exp : rest) success failure = do
  exp' <- dsExp exp
  success' <- dsGuardStmts rest success failure
  return $ DCaseE exp' [ DMatch (DConPa 'True []) success'
                       , DMatch (DConPa 'False []) failure ]
dsGuardStmts (ParS _ : _) _ _ = impossible "Parallel comprehension in a pattern guard."

-- | Desugar the @Stmt@s in a @do@ expression
dsDoStmts :: DsMonad q => [Stmt] -> q DExp
dsDoStmts [] = impossible "do-expression ended with something other than bare statement."
dsDoStmts [NoBindS exp] = dsExp exp
dsDoStmts (BindS pat exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsDoStmts rest
  DAppE (DAppE (DVarE '(>>=)) exp') <$> dsLam [pat] rest'
dsDoStmts (LetS decs : rest) = DLetE <$> dsLetDecs decs <*> dsDoStmts rest
dsDoStmts (NoBindS exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsDoStmts rest
  return $ DAppE (DAppE (DVarE '(>>)) exp') rest'
dsDoStmts (ParS _ : _) = impossible "Parallel comprehension in a do-statement."

-- | Desugar the @Stmt@s in a list or monad comprehension
dsComp :: DsMonad q => [Stmt] -> q DExp
dsComp [] = impossible "List/monad comprehension ended with something other than a bare statement."
dsComp [NoBindS exp] = DAppE (DVarE 'return) <$> dsExp exp
dsComp (BindS pat exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsComp rest
  DAppE (DAppE (DVarE '(>>=)) exp') <$> dsLam [pat] rest'
dsComp (LetS decs : rest) = DLetE <$> dsLetDecs decs <*> dsComp rest
dsComp (NoBindS exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsComp rest
  return $ DAppE (DAppE (DVarE '(>>)) (DAppE (DVarE 'guard) exp')) rest'
dsComp (ParS stmtss : rest) = do
  (pat, exp) <- dsParComp stmtss
  rest' <- dsComp rest
  DAppE (DAppE (DVarE '(>>=)) exp) <$> dsLam [pat] rest'

-- | Desugar the contents of a parallel comprehension.
--   Returns a @Pat@ containing a tuple of all bound variables and an expression
--   to produce the values for those variables
dsParComp :: DsMonad q => [[Stmt]] -> q (Pat, DExp)
dsParComp [] = impossible "Empty list of parallel comprehension statements."
dsParComp [r] = do
  let rv = foldMap extractBoundNamesStmt r
  dsR <- dsComp (r ++ [mk_tuple_stmt rv])
  return (mk_tuple_pat rv, dsR)
dsParComp (q : rest) = do
  let qv = foldMap extractBoundNamesStmt q
  (rest_pat, rest_exp) <- dsParComp rest
  dsQ <- dsComp (q ++ [mk_tuple_stmt qv])
  let zipped = DAppE (DAppE (DVarE 'mzip) dsQ) rest_exp
  return (ConP (tupleDataName 2) [mk_tuple_pat qv, rest_pat], zipped)

-- helper function for dsParComp
mk_tuple_stmt :: S.Set Name -> Stmt
mk_tuple_stmt name_set =
  NoBindS (mkTupleExp (S.foldr ((:) . VarE) [] name_set))

-- helper function for dsParComp
mk_tuple_pat :: S.Set Name -> Pat
mk_tuple_pat name_set =
  mkTuplePat (S.foldr ((:) . VarP) [] name_set)

-- | Desugar a pattern, along with processing a (desugared) expression that
-- is the entire scope of the variables bound in the pattern.
dsPatOverExp :: DsMonad q => Pat -> DExp -> q (DPat, DExp)
dsPatOverExp pat exp = do
  (pat', vars) <- runWriterT $ dsPat pat
  let name_decs = uncurry (zipWith (DValD . DVarPa)) $ unzip vars
  return (pat', maybeDLetE name_decs exp)

-- | Desugar multiple patterns. Like 'dsPatOverExp'.
dsPatsOverExp :: DsMonad q => [Pat] -> DExp -> q ([DPat], DExp)
dsPatsOverExp pats exp = do
  (pats', vars) <- runWriterT $ mapM dsPat pats
  let name_decs = uncurry (zipWith (DValD . DVarPa)) $ unzip vars
  return (pats', maybeDLetE name_decs exp)

-- | Desugar a pattern, returning a list of (Name, DExp) pairs of extra
-- variables that must be bound within the scope of the pattern
dsPatX :: DsMonad q => Pat -> q (DPat, [(Name, DExp)])
dsPatX = runWriterT . dsPat

-- | Desugaring a pattern also returns the list of variables bound in as-patterns
-- and the values they should be bound to. This variables must be brought into
-- scope in the "body" of the pattern.
type PatM q = WriterT [(Name, DExp)] q

-- | Desugar a pattern.
dsPat :: DsMonad q => Pat -> PatM q DPat
dsPat (LitP lit) = return $ DLitPa lit
dsPat (VarP n) = return $ DVarPa n
dsPat (TupP pats) = DConPa (tupleDataName (length pats)) <$> mapM dsPat pats
dsPat (UnboxedTupP pats) = DConPa (unboxedTupleDataName (length pats)) <$>
                           mapM dsPat pats
dsPat (ConP name pats) = DConPa name <$> mapM dsPat pats
dsPat (InfixP p1 name p2) = DConPa name <$> mapM dsPat [p1, p2]
dsPat (UInfixP _ _ _) =
  fail "Cannot desugar unresolved infix operators."
dsPat (ParensP pat) = dsPat pat
dsPat (TildeP pat) = DTildePa <$> dsPat pat
dsPat (BangP pat) = DBangPa <$> dsPat pat
dsPat (AsP name pat) = do
  pat' <- dsPat pat
  pat'' <- lift $ removeWilds pat'
  tell [(name, dPatToDExp pat'')]
  return pat''
dsPat WildP = return DWildPa
dsPat (RecP con_name field_pats) = do
  con <- lift $ dataConNameToCon con_name
  reordered <- case con of
    RecC _name fields -> reorderFieldsPat fields field_pats
    _ -> lift $ impossible $ "Record syntax used with non-record constructor "
                             ++ (show con_name) ++ "."
  return $ DConPa con_name reordered
dsPat (ListP pats) = go pats
  where go [] = return $ DConPa '[] []
        go (h : t) = do
          h' <- dsPat h
          t' <- go t
          return $ DConPa '(:) [h', t']
dsPat (SigP _ _) =
  lift $ impossible
             ("At last check (Aug 2013), type patterns in signatures are not\n" ++
              "supported in GHC. They are not supported in th-desugar either.")
dsPat (ViewP _ _) =
  fail "View patterns are not supported in th-desugar. Use pattern guards instead."

-- | Convert a 'DPat' to a 'DExp'. Fails on 'DWildP'.
dPatToDExp :: DPat -> DExp
dPatToDExp (DLitPa lit) = DLitE lit
dPatToDExp (DVarPa name) = DVarE name
dPatToDExp (DConPa name pats) = foldl DAppE (DConE name) (map dPatToDExp pats)
dPatToDExp (DTildePa pat) = dPatToDExp pat
dPatToDExp (DBangPa pat) = dPatToDExp pat
dPatToDExp DWildPa = error "Internal error in th-desugar: wildcard in rhs of as-pattern"

-- | Remove all wildcards from a pattern, replacing any wildcard with a fresh
--   variable
removeWilds :: DsMonad q => DPat -> q DPat
removeWilds p@(DLitPa _) = return p
removeWilds p@(DVarPa _) = return p
removeWilds (DConPa con_name pats) = DConPa con_name <$> mapM removeWilds pats
removeWilds (DTildePa pat) = DTildePa <$> removeWilds pat
removeWilds (DBangPa pat) = DBangPa <$> removeWilds pat
removeWilds DWildPa = DVarPa <$> newUniqueName "wild"

-- | Desugar @Info@
dsInfo :: DsMonad q => Info -> q DInfo
dsInfo (ClassI dec instances) = do
  [ddec]     <- dsDec dec
  dinstances <- dsDecs instances
  return $ DTyConI ddec (Just dinstances)
dsInfo (ClassOpI name ty parent fixity) =
  DVarI name <$> dsType ty <*> pure (Just parent) <*> pure fixity
dsInfo (TyConI dec) = do
  [ddec] <- dsDec dec
  return $ DTyConI ddec Nothing
dsInfo (FamilyI dec instances) = do
  [ddec]     <- dsDec dec
  dinstances <- dsDecs instances
  (ddec', num_args) <- fixBug8884ForFamilies ddec
  let dinstances' = map (fixBug8884ForInstances num_args) dinstances
  return $ DTyConI ddec' (Just dinstances')
dsInfo (PrimTyConI name arity unlifted) =
  return $ DPrimTyConI name arity unlifted
dsInfo (DataConI name ty parent fixity) =
  DVarI name <$> dsType ty <*> pure (Just parent) <*> pure fixity
dsInfo (VarI name ty Nothing fixity) =
  DVarI name <$> dsType ty <*> pure Nothing <*> pure fixity
dsInfo (VarI name _ (Just _) _) =
  impossible $ "Declaration supplied with variable: " ++ show name
dsInfo (TyVarI name ty) = DTyVarI name <$> dsKind ty

fixBug8884ForFamilies :: DsMonad q => DDec -> q (DDec, Int)
#if __GLASGOW_HASKELL__ < 708
fixBug8884ForFamilies (DFamilyD flav name tvbs m_kind) = do
  let num_args = length tvbs
  m_kind' <- mapM (remove_arrows num_args) m_kind
  return (DFamilyD flav name tvbs m_kind', num_args)
fixBug8884ForFamilies (DClosedTypeFamilyD name tvbs m_kind eqns) = do
  let num_args = length tvbs
      eqns' = map (fixBug8884ForEqn num_args) eqns
  m_kind' <- mapM (remove_arrows num_args) m_kind
  return (DClosedTypeFamilyD name tvbs m_kind' eqns', num_args)
fixBug8884ForFamilies dec =
  impossible $ "Reifying yielded a FamilyI with a non-family Dec: " ++ show dec

remove_arrows :: DsMonad q => Int -> DKind -> q DKind
remove_arrows 0 k = return k
remove_arrows n (DArrowK _ k) = remove_arrows (n-1) k
remove_arrows _ _ =
  impossible "Internal error: Fix for bug 8884 ran out of arrows."
  
#else
fixBug8884ForFamilies dec = return (dec, 0)   -- return value ignored
#endif

fixBug8884ForInstances :: Int -> DDec -> DDec
fixBug8884ForInstances num_args (DTySynInstD name eqn) =
  DTySynInstD name (fixBug8884ForEqn num_args eqn)
fixBug8884ForInstances _ dec = dec

fixBug8884ForEqn :: Int -> DTySynEqn -> DTySynEqn
#if __GLASGOW_HASKELL__ < 708
fixBug8884ForEqn num_args (DTySynEqn lhs rhs) =
  let lhs' = drop (length lhs - num_args) lhs in
  DTySynEqn lhs' rhs
#else
fixBug8884ForEqn _ = id
#endif

-- | Desugar arbitrary @Dec@s
dsDecs :: DsMonad q => [Dec] -> q [DDec]
dsDecs = concatMapM dsDec

-- | Desugar a single @Dec@, perhaps producing multiple 'DDec's
dsDec :: DsMonad q => Dec -> q [DDec]
dsDec d@(FunD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec d@(ValD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec (DataD cxt n tvbs cons derivings) =
  (:[]) <$> (DDataD Data <$> dsCxt cxt <*> pure n
                         <*> mapM dsTvb tvbs <*> mapM dsCon cons
                         <*> pure derivings)
dsDec (NewtypeD cxt n tvbs con derivings) =
  (:[]) <$> (DDataD Newtype <$> dsCxt cxt <*> pure n
                            <*> mapM dsTvb tvbs <*> ((:[]) <$> dsCon con)
                            <*> pure derivings)
dsDec (TySynD n tvbs ty) =
  (:[]) <$> (DTySynD n <$> mapM dsTvb tvbs <*> dsType ty)
dsDec (ClassD cxt n tvbs fds decs) =
  (:[]) <$> (DClassD <$> dsCxt cxt <*> pure n <*> mapM dsTvb tvbs
                     <*> pure fds <*> dsDecs decs)
dsDec (InstanceD cxt ty decs) =
  (:[]) <$> (DInstanceD <$> dsCxt cxt <*> dsType ty <*> dsDecs decs)
dsDec d@(SigD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec (ForeignD f) = (:[]) <$> (DForeignD <$> dsForeign f)
dsDec d@(InfixD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec (PragmaD prag) = (:[]) <$> (DPragmaD <$> dsPragma prag)
dsDec (FamilyD flav n tvbs m_k) =
  (:[]) <$> (DFamilyD flav n <$> mapM dsTvb tvbs <*> mapM dsKind m_k)
dsDec (DataInstD cxt n tys cons derivings) =
  (:[]) <$> (DDataInstD Data <$> dsCxt cxt <*> pure n <*> mapM dsType tys
                             <*> mapM dsCon cons <*> pure derivings)
dsDec (NewtypeInstD cxt n tys con derivings) =
  (:[]) <$> (DDataInstD Newtype <$> dsCxt cxt <*> pure n <*> mapM dsType tys
                                <*> ((:[]) <$> dsCon con) <*> pure derivings)
#if __GLASGOW_HASKELL__ < 707
dsDec (TySynInstD n lhs rhs) = (:[]) <$> (DTySynInstD n <$>
                                          (DTySynEqn <$> mapM dsType lhs
                                                     <*> dsType rhs))
#else
dsDec (TySynInstD n eqn) = (:[]) <$> (DTySynInstD n <$> dsTySynEqn eqn)
dsDec (ClosedTypeFamilyD n tvbs m_k eqns) =
  (:[]) <$> (DClosedTypeFamilyD n <$> mapM dsTvb tvbs <*> mapM dsKind m_k
                                  <*> mapM dsTySynEqn eqns)
dsDec (RoleAnnotD n roles) = return [DRoleAnnotD n roles]
#endif
             
-- | Desugar @Dec@s that can appear in a let expression
dsLetDecs :: DsMonad q => [Dec] -> q [DLetDec]
dsLetDecs = concatMapM dsLetDec

-- | Desugar a single @Dec@, perhaps producing multiple 'DLetDec's
dsLetDec :: DsMonad q => Dec -> q [DLetDec]
dsLetDec (FunD name clauses) = do
  clauses' <- dsClauses name clauses
  return [DFunD name clauses']
dsLetDec (ValD pat body where_decs) = do
  (pat', vars) <- dsPatX pat
  body' <- dsBody body where_decs error_exp
  let extras = uncurry (zipWith (DValD . DVarPa)) $ unzip vars
  return $ DValD pat' body' : extras
  where
    error_exp = DAppE (DVarE 'error) (DLitE
                       (StringL $ "Non-exhaustive patterns for " ++ pprint pat))
dsLetDec (SigD name ty) = do
  ty' <- dsType ty
  return [DSigD name ty']
dsLetDec (InfixD fixity name) = return [DInfixD fixity name]
dsLetDec _dec = impossible "Illegal declaration in let expression."

-- | Desugar a single @Con@.
dsCon :: DsMonad q => Con -> q DCon
dsCon (NormalC n stys) = DCon [] [] n <$> (DNormalC <$> mapM (liftSndM dsType) stys)
dsCon (RecC n vstys) = DCon [] [] n <$> (DRecC <$> mapM (liftThdOf3M dsType) vstys)
dsCon (InfixC (s1, ty1) n (s2, ty2)) = do
  dty1 <- dsType ty1
  dty2 <- dsType ty2
  return $ DCon [] [] n (DNormalC [(s1, dty1), (s2, dty2)])
dsCon (ForallC tvbs cxt con) = do
  dtvbs <- mapM dsTvb tvbs
  dcxt <- dsCxt cxt
  DCon dtvbs' dcxt' n fields <- dsCon con
  return $ DCon (dtvbs ++ dtvbs') (dcxt ++ dcxt') n fields

-- | Desugar a @Foreign@.
dsForeign :: DsMonad q => Foreign -> q DForeign
dsForeign (ImportF cc safety str n ty) = DImportF cc safety str n <$> dsType ty
dsForeign (ExportF cc str n ty)        = DExportF cc str n <$> dsType ty

-- | Desugar a @Pragma@.
dsPragma :: DsMonad q => Pragma -> q DPragma
dsPragma (InlineP n inl rm phases)       = return $ DInlineP n inl rm phases
dsPragma (SpecialiseP n ty m_inl phases) = DSpecialiseP n <$> dsType ty
                                                          <*> pure m_inl
                                                          <*> pure phases
dsPragma (SpecialiseInstP ty)            = DSpecialiseInstP <$> dsType ty
dsPragma (RuleP str rbs lhs rhs phases)  = DRuleP str <$> mapM dsRuleBndr rbs
                                                      <*> dsExp lhs
                                                      <*> dsExp rhs
                                                      <*> pure phases
#if __GLASGOW_HASKELL__ >= 707
dsPragma (AnnP target exp)               = DAnnP target <$> dsExp exp
#endif

-- | Desugar a @RuleBndr@.
dsRuleBndr :: DsMonad q => RuleBndr -> q DRuleBndr
dsRuleBndr (RuleVar n)         = return $ DRuleVar n
dsRuleBndr (TypedRuleVar n ty) = DTypedRuleVar n <$> dsType ty

#if __GLASGOW_HASKELL__ >= 707
-- | Desugar a @TySynEqn@. (Available only with GHC 7.8+)
dsTySynEqn :: DsMonad q => TySynEqn -> q DTySynEqn
dsTySynEqn (TySynEqn lhs rhs) = DTySynEqn <$> mapM dsType lhs <*> dsType rhs
#endif

-- | Desugar clauses to a function definition
dsClauses :: DsMonad q
          => Name         -- ^ Name of the function
          -> [Clause]     -- ^ Clauses to desugar
          -> q [DClause]
dsClauses _ [] = return []
dsClauses n (Clause pats (NormalB exp) where_decs : rest) = do
  -- this is just a convenience optimization; we could tuple up all the patterns
  rest' <- dsClauses n rest
  exp' <- dsExp exp
  where_decs' <- dsLetDecs where_decs
  let exp_with_wheres = maybeDLetE where_decs' exp'
  (pats', exp'') <- dsPatsOverExp pats exp_with_wheres
  return $ DClause pats' exp'' : rest'
dsClauses n clauses@(Clause outer_pats _ _ : _) = do
  arg_names <- replicateM (length outer_pats) (newUniqueName "arg")
  let scrutinee = mkTupleDExp (map DVarE arg_names)
  clause <- DClause (map DVarPa arg_names) <$>
              (DCaseE scrutinee <$> foldrM (clause_to_dmatch scrutinee) [] clauses)
  return [clause]
  where
    clause_to_dmatch :: DsMonad q => DExp -> Clause -> [DMatch] -> q [DMatch]
    clause_to_dmatch scrutinee (Clause pats body where_decs) failure_matches = do
      let failure_exp = maybeDCaseE ("Non-exhaustive patterns in " ++ (show n))
                                    scrutinee failure_matches
      exp <- dsBody body where_decs failure_exp
      (pats', exp') <- dsPatsOverExp pats exp
      uni_pats <- fmap getAll $ concatMapM (fmap All . isUniversalPattern) pats'
      let match = DMatch (mkTupleDPat pats') exp'
      if uni_pats
      then return [match]
      else return (match : failure_matches)

-- | Desugar a type
dsType :: DsMonad q => Type -> q DType
dsType (ForallT tvbs preds ty) = DForallT <$> mapM dsTvb tvbs <*> dsCxt preds <*> dsType ty
dsType (AppT t1 t2) = DAppT <$> dsType t1 <*> dsType t2
dsType (SigT ty ki) = DSigT <$> dsType ty <*> dsKind ki
dsType (VarT name) = return $ DVarT name
dsType (ConT name) = return $ DConT name
  -- the only difference between ConT and PromotedT is the name lookup. Here, we assume
  -- that the TH quote mechanism figured out the right name. Note that lookupDataName name
  -- does not necessarily work, because `name` has its original module attached, which
  -- may not be in scope.
dsType (PromotedT name) = return $ DConT name
dsType (TupleT n) = return $ DConT (tupleTypeName n)
dsType (UnboxedTupleT n) = return $ DConT (unboxedTupleTypeName n)
dsType ArrowT = return DArrowT
dsType ListT = return $ DConT ''[]
dsType (PromotedTupleT n) = return $ DConT (tupleDataName n)
dsType PromotedNilT = return $ DConT '[]
dsType PromotedConsT = return $ DConT '(:)
dsType StarT = impossible "The kind * seen in a type."
dsType ConstraintT = impossible "The kind `Constraint' seen in a type."
dsType (LitT lit) = return $ DLitT lit
#if __GLASGOW_HASKELL__ >= 709
dsType EqualityT = return $ DConT ''(~)
#endif

-- | Desugar a @TyVarBndr@
dsTvb :: DsMonad q => TyVarBndr -> q DTyVarBndr
dsTvb (PlainTV n) = return $ DPlainTV n
dsTvb (KindedTV n k) = DKindedTV n <$> dsKind k

-- | Desugar a @Cxt@
dsCxt :: DsMonad q => Cxt -> q DCxt
dsCxt = concatMapM dsPred

-- | Desugar a @Pred@, flattening any internal tuples
dsPred :: DsMonad q => Pred -> q DCxt
#if __GLASGOW_HASKELL__ < 709
dsPred (ClassP n tys) = do
  ts' <- mapM dsType tys
  return [foldl DAppPr (DConPr n) ts']
dsPred (EqualP t1 t2) = do
  ts' <- mapM dsType [t1, t2]
  return [foldl DAppPr (DConPr ''(~)) ts']
#else
dsPred t
  | Just ts <- splitTuple_maybe t
  = concatMapM dsPred ts
dsPred t@(ForallT _ _ _) = impossible $ "Forall seen in constraint: " ++ show t
dsPred (AppT t1 t2) = do
  [p1] <- dsPred t1   -- tuples can't be applied!
  (:[]) <$> DAppPr p1 <$> dsType t2
dsPred (SigT ty ki) = do
  preds <- dsPred ty
  case preds of
    [p]   -> (:[]) <$> DSigPr p <$> dsKind ki
    other -> return other   -- just drop the kind signature on a tuple.
dsPred (VarT n) = return [DVarPr n]
dsPred (ConT n) = return [DConPr n]
dsPred t@(PromotedT _) =
  impossible $ "Promoted type seen as head of constraint: " ++ show t
dsPred (TupleT 0) = return [DConPr (tupleTypeName 0)]
dsPred (TupleT _) =
  impossible "Internal error in th-desugar in detecting tuple constraints."
dsPred t@(UnboxedTupleT _) =
  impossible $ "Unboxed tuple seen as head of constraint: " ++ show t
dsPred ArrowT = impossible "Arrow seen as head of constraint."
dsPred ListT  = impossible "List seen as head of constraint."
dsPred (PromotedTupleT _) =
  impossible "Promoted tuple seen as head of constraint."
dsPred PromotedNilT  = impossible "Promoted nil seen as head of constraint."
dsPred PromotedConsT = impossible "Promoted cons seen as head of constraint."
dsPred StarT         = impossible "* seen as head of constraint."
dsPred ConstraintT =
  impossible "The kind `Constraint' seen as head of constraint."
dsPred t@(LitT _) =
  impossible $ "Type literal seen as head of constraint: " ++ show t
dsPred EqualityT = return [DConPr ''(~)]
#endif

-- | Desugar a kind
dsKind :: DsMonad q => Kind -> q DKind
dsKind (ForallT tvbs cxt ki)
  | [] <- cxt
  , Just names <- mapM stripPlainTV_maybe tvbs
  = DForallK names <$> dsKind ki

  | otherwise
  = impossible "Annotations of kind variables or kind constraints."
dsKind (AppT (AppT ArrowT k1) k2) = DArrowK <$> dsKind k1 <*> dsKind k2
dsKind (AppT k1 k2) = do
  k1' <- dsKind k1
  (con_name, args) <- case k1' of
                        DConK n as -> return (n, as)
                        _ -> impossible "Illegal kind application."
  k2' <- dsKind k2
  return $ DConK con_name (args ++ [k2'])
dsKind k@(SigT _ _) = impossible $ "Super-kind signature in kind " ++ (pprint k)
dsKind (VarT name) = return $ DVarK name
dsKind (ConT name) = return $ DConK name []
dsKind (PromotedT name) = impossible $ "Promoted data constructor " ++ show name ++ " in kind."
dsKind (TupleT n) = return $ DConK (tupleTypeName n) []
dsKind (UnboxedTupleT _) = impossible "Unboxed tuple kind."
dsKind ArrowT = impossible "Unsaturated (->) in kind."
dsKind ListT = return $ DConK ''[] []
dsKind (PromotedTupleT _) = impossible "Promoted tuple used as a kind."
dsKind PromotedNilT = impossible "Promoted [] used as a kind."
dsKind PromotedConsT = impossible "Promoted (:) used as a kind."
dsKind StarT = return DStarK
dsKind ConstraintT = return $ DConK ''Constraint []
dsKind (LitT _) = impossible "Literal used in a kind."
#if __GLASGOW_HASKELL__ >= 709
dsKind EqualityT = impossible "(~) used in a kind."
#endif

-- | Like 'reify', but safer and desugared. Uses local declarations where
-- available.
dsReify :: DsMonad q => Name -> q (Maybe DInfo)
dsReify = traverse dsInfo <=< reifyWithLocals_maybe
  
-- create a list of expressions in the same order as the fields in the first argument
-- but with the values as given in the second argument
-- if a field is missing from the second argument, use the corresponding expression
-- from the third argument
reorderFields :: DsMonad q => [VarStrictType] -> [FieldExp] -> [DExp] -> q [DExp]
reorderFields = reorderFields' dsExp

reorderFieldsPat :: DsMonad q => [VarStrictType] -> [FieldPat] -> PatM q [DPat]
reorderFieldsPat field_decs field_pats =
  reorderFields' dsPat field_decs field_pats (repeat DWildPa)

reorderFields' :: (Applicative m, Monad m)
               => (a -> m da)
               -> [VarStrictType] -> [(Name, a)]
               -> [da] -> m [da]
reorderFields' _ [] _ _ = return []
reorderFields' ds_thing ((field_name, _, _) : rest)
               field_things (deflt : rest_deflt) = do
  rest' <- reorderFields' ds_thing rest field_things rest_deflt
  case find (\(thing_name, _) -> thing_name == field_name) field_things of
    Just (_, thing) -> (: rest') <$> ds_thing thing
    Nothing -> return $ deflt : rest'
reorderFields' _ (_ : _) _ [] = error "Internal error in th-desugar."

-- | Make a tuple 'DExp' from a list of 'DExp's. Avoids using a 1-tuple.
mkTupleDExp :: [DExp] -> DExp
mkTupleDExp [exp] = exp
mkTupleDExp exps = foldl DAppE (DConE $ tupleDataName (length exps)) exps

-- | Make a tuple 'Exp' from a list of 'Exp's. Avoids using a 1-tuple.
mkTupleExp :: [Exp] -> Exp
mkTupleExp [exp] = exp
mkTupleExp exps = foldl AppE (ConE $ tupleDataName (length exps)) exps

-- | Make a tuple 'DPat' from a list of 'DPat's. Avoids using a 1-tuple.
mkTupleDPat :: [DPat] -> DPat
mkTupleDPat [pat] = pat
mkTupleDPat pats = DConPa (tupleDataName (length pats)) pats

-- | Make a tuple 'Pat' from a list of 'Pat's. Avoids using a 1-tuple.
mkTuplePat :: [Pat] -> Pat
mkTuplePat [pat] = pat
mkTuplePat pats = ConP (tupleDataName (length pats)) pats

-- | Is this pattern guaranteed to match?
isUniversalPattern :: DsMonad q => DPat -> q Bool
isUniversalPattern (DLitPa {}) = return False
isUniversalPattern (DVarPa {}) = return True
isUniversalPattern (DConPa con_name pats) = do
  data_name <- dataConNameToDataName con_name
  (_tvbs, cons) <- getDataD "Internal error." data_name
  if length cons == 1
  then fmap and $ mapM isUniversalPattern pats
  else return False
isUniversalPattern (DTildePa {}) = return True
isUniversalPattern (DBangPa pat) = isUniversalPattern pat
isUniversalPattern DWildPa       = return True

-- | Apply one 'DExp' to a list of arguments
applyDExp :: DExp -> [DExp] -> DExp
applyDExp = foldl DAppE

-- | Apply one 'DType' to a list of arguments
applyDType :: DType -> [DType] -> DType
applyDType = foldl DAppT
