{- Language/Haskell/TH/Desugar/Core.hs

(c) Richard Eienberg 2013
eir@cis.upenn.edu

Desugars full Template Haskell syntax into a smaller core syntax for further
processing. The desugared types and constructors are prefixed with a D.
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, CPP #-}

module Language.Haskell.TH.Desugar.Core where

import Prelude hiding (mapM, foldl, foldr, all, elem)

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Control.Applicative
import Control.Monad hiding (mapM)
import Control.Monad.Zip
import Data.Foldable
import Data.Traversable

import qualified Data.Set as S
import GHC.Exts

import Language.Haskell.TH.Desugar.Util

-- | Corresponds to TH's @Exp@ type. Note that @DLamE@ takes names, not patterns.
data DExp = DVarE Name
          | DConE Name
          | DLitE Lit
          | DAppE DExp DExp
          | DLamE [Name] DExp
          | DCaseE DExp [DMatch]
          | DLetE [DLetDec] DExp
          | DSigE DExp DType

-- | Declarations as used in a @let@ statement. Other @Dec@s are not desugared.
data DLetDec = DFunD Name [DClause]
             | DValD DPat DExp
             | DSigD Name DType
             | DInfixD Fixity Name

-- | Corresponds to TH's @Pat@ type.
data DPat = DLitP Lit
          | DVarP Name
          | DConP Name [DPat]
          | DTildeP DPat
          | DBangP DPat
          | DWildP
          | DSigP DPat DType

-- | Corresponds to TH's @Type@ type.
data DType = DForallT [DTyVarBndr] DCxt DType
           | DAppT DType DType
           | DSigT DType DKind
           | DVarT Name
           | DConT Name
           | DArrowT
           | DLitT TyLit

-- | Corresponds to TH's @Kind@ type, which is a synonym for @Type@. 'DKind', though,
--   only contains constructors that make sense for kinds.
data DKind = DForallK [Name] DKind
           | DVarK Name
           | DConK Name [DKind]
           | DArrowK DKind DKind
           | DStarK

-- | Corresponds to TH's @Cxt@
type DCxt = [DPred]

-- | Corresponds to TH's @Pred@
data DPred = DClassP Name [DType]
           | DEqualP DType DType

-- | Corresponds to TH's @TyVarBndr@. Note that @PlainTV x@ and @KindedTV x StarT@ are
--   distinct, so we retain that distinction here.
data DTyVarBndr = DPlainTV Name
                | DKindedTV Name DKind
#if __GLASGOW_HASKELL__ >= 707
                | DRoledTV Name Role
                | DKindedRoledTV Name DKind Role
#endif

-- | Corresponds to TH's @Match@ type.
data DMatch = DMatch DPat DExp

-- | Corresponds to TH's @Clause@ type.
data DClause = DClause [DPat] DExp

-- | Desugar an expression
dsExp :: Exp -> Q DExp
dsExp (VarE n) = return $ DVarE n
dsExp (ConE n) = return $ DConE n
dsExp (LitE lit) = return $ DLitE lit
dsExp (AppE e1 e2) = DAppE <$> dsExp e1 <*> dsExp e2
dsExp (InfixE Nothing op Nothing) = dsExp op
dsExp (InfixE (Just lhs) op Nothing) = DAppE <$> (dsExp op) <*> (dsExp lhs)
dsExp (InfixE Nothing op (Just rhs)) = do
  lhsName <- newName "lhs"
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
  x <- newName "x"
  matches' <- dsMatches x matches
  return $ DLamE [x] (DCaseE (DVarE x) matches')
dsExp (TupE exps) = do
  exps' <- mapM dsExp exps
  return $ foldl DAppE (DConE $ tupleDataName (length exps)) exps'
dsExp (UnboxedTupE exps) =
  foldl DAppE (DConE $ unboxedTupleDataName (length exps)) <$> mapM dsExp exps
dsExp (CondE e1 e2 e3) = do
  e1' <- dsExp e1
  e2' <- dsExp e2
  e3' <- dsExp e3
  return $ DCaseE e1' [DMatch (DConP 'True []) e2', DMatch (DConP 'False []) e3']
dsExp (MultiIfE guarded_exps) =
  let failure = DAppE (DVarE 'error) (DLitE (StringL "None-exhaustive guards in multi-way if")) in
  dsGuards guarded_exps failure
dsExp (LetE decs exp) = DLetE <$> mapM dsLetDec decs <*> dsExp exp
dsExp (CaseE exp matches) = do
  scrutinee <- newName "scrutinee"
  exp' <- dsExp exp
  matches' <- dsMatches scrutinee matches
  return $ DLetE [DValD (DVarP scrutinee) exp'] $
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
  info <- reifyWithWarning first_name
  applied_type <- case info of
                    VarI _name ty _m_dec _fixity -> extract_first_arg ty
                    _ -> impossible "Record update with an invalid field name."
  type_name <- extract_type_name applied_type
  (_, cons) <- getDataD "This seems to be an error in GHC." type_name
  let filtered_cons = filter_cons_with_names cons (map fst field_exps)
  exp' <- dsExp exp
  matches <- mapM con_to_dmatch filtered_cons
  return $ DCaseE exp' (matches ++ [error_match])
  where
    extract_first_arg :: Type -> Q Type
    extract_first_arg (AppT (AppT ArrowT arg) _) = return arg
    extract_first_arg (ForallT _ _ t) = extract_first_arg t
    extract_first_arg (SigT t _) = extract_first_arg t
    extract_first_arg _ = impossible "Record selector not a function."

    extract_type_name :: Type -> Q Name
    extract_type_name (AppT t1 _) = extract_type_name t1
    extract_type_name (SigT t _) = extract_type_name t
    extract_type_name (ConT n) = return n
    extract_type_name _ = impossible "Record selector domain not a datatype."
    
    filter_cons_with_names cons field_names =
      filter (\case RecC _con_name args -> let con_field_names = map fst_of_3 args in
                                           all (`elem` con_field_names) field_names
                    _ -> False) cons

    con_to_dmatch :: Con -> Q DMatch
    con_to_dmatch (RecC con_name args) = do
      let con_field_names = map fst_of_3 args
      field_var_names <- mapM (newName . nameBase) con_field_names
      DMatch (DConP con_name (map DVarP field_var_names)) <$>
             (foldl DAppE (DConE con_name) <$>
                    (reorderFields args field_exps (map DVarE field_var_names)))
    con_to_dmatch _ = impossible "Internal error within th-desugar."

    error_match = DMatch DWildP (DAppE (DVarE 'error)
                    (DLitE (StringL "Non-exhaustive patterns in record update")))

    fst_of_3 (x, _, _) = x

-- | Desugar a lambda expression, where the body has already been desugared
dsLam :: [Pat] -> DExp -> Q DExp
dsLam pats exp
  | Just names <- mapM stripVarP_maybe pats
  = return $ DLamE names exp
  | otherwise
  = do let num_args = length pats
       arg_names <- replicateM num_args (newName "arg")
       let scrutinee = foldl DAppE (DConE $ tupleDataName num_args) (map DVarE arg_names)
       (pats', xform) <- dsPats pats
       let match = DMatch (DConP (tupleDataName num_args) pats') (xform exp)
       return $ DLamE arg_names (DCaseE scrutinee [match])

-- | Desugar a list of matches for a @case@ statement
dsMatches :: Name     -- ^ Name of the scrutinee, which must be a bare var
          -> [Match]  -- ^ Matches of the @case@ statement
          -> Q [DMatch]
dsMatches scr = go
  where
    go :: [Match] -> Q [DMatch]
    go [] = return []
    go (Match pat body where_decs : rest) = do
      rest' <- go rest
      let failure = DCaseE (DVarE scr) rest'  -- this might be an empty case.
      exp' <- dsBody body where_decs failure
      (pat', xform) <- dsPat pat
      return (DMatch pat' (xform exp') : rest')

-- | Desugar a @Body@
dsBody :: Body      -- ^ body to desugar
       -> [Dec]     -- ^ "where" declarations
       -> DExp      -- ^ what to do if the guards don't match
       -> Q DExp
dsBody (NormalB exp) decs _ = DLetE <$> mapM dsLetDec decs <*> dsExp exp
dsBody (GuardedB guarded_exps) decs failure =
  DLetE <$> mapM dsLetDec decs <*> dsGuards guarded_exps failure

-- | Desugar guarded expressions
dsGuards :: [(Guard, Exp)]  -- ^ Guarded expressions
         -> DExp            -- ^ What to do if none of the guards match
         -> Q DExp
dsGuards [] thing_inside = return thing_inside
dsGuards ((NormalG guard, exp) : rest) thing_inside =
  dsGuards ((PatG [NoBindS guard], exp) : rest) thing_inside
dsGuards ((PatG stmts, exp) : rest) thing_inside = do
  success <- dsExp exp
  failure <- dsGuards rest thing_inside
  dsGuardStmts stmts success failure

-- | Desugar the @Stmt@s in a guard
dsGuardStmts :: [Stmt]  -- ^ The @Stmt@s to desugar
             -> DExp    -- ^ What to do if the @Stmt@s yield success
             -> DExp    -- ^ What to do if the @Stmt@s yield failure
             -> Q DExp
dsGuardStmts [] success _failure = return success
dsGuardStmts (BindS pat exp : rest) success failure = do
  (pat', xform) <- dsPat pat
  exp' <- dsExp exp
  success' <- dsGuardStmts rest success failure
  return $ DCaseE exp' [DMatch pat' (xform success'), DMatch DWildP failure]
dsGuardStmts (LetS decs : rest) success failure = do
  decs' <- mapM dsLetDec decs
  success' <- dsGuardStmts rest success failure
  return $ DLetE decs' success'
dsGuardStmts (NoBindS exp : rest) success failure = do
  exp' <- dsExp exp
  success' <- dsGuardStmts rest success failure
  return $ DCaseE exp' [ DMatch (DConP 'True []) success'
                       , DMatch (DConP 'False []) failure ]
dsGuardStmts (ParS _ : _) _ _ = impossible "Parallel comprehension in a pattern guard."

-- | Desugar the @Stmt@s in a @do@ expression
dsDoStmts :: [Stmt] -> Q DExp
dsDoStmts [] = impossible "do-expression ended with something other than bare statement."
dsDoStmts [NoBindS exp] = dsExp exp
dsDoStmts (BindS pat exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsDoStmts rest
  DAppE (DAppE (DVarE '(>>=)) exp') <$> dsLam [pat] rest'
dsDoStmts (LetS decs : rest) = DLetE <$> mapM dsLetDec decs <*> dsDoStmts rest
dsDoStmts (NoBindS exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsDoStmts rest
  return $ DAppE (DAppE (DVarE '(>>)) exp') rest'
dsDoStmts (ParS _ : _) = impossible "Parallel comprehension in a do-statement."

-- | Desugar the @Stmt@s in a list or monad comprehension
dsComp :: [Stmt] -> Q DExp
dsComp [] = impossible "List/monad comprehension ended with something other than a bare statement."
dsComp [NoBindS exp] = DAppE (DVarE 'return) <$> dsExp exp
dsComp (BindS pat exp : rest) = do
  exp' <- dsExp exp
  rest' <- dsComp rest
  DAppE (DAppE (DVarE '(>>=)) exp') <$> dsLam [pat] rest'
dsComp (LetS decs : rest) = DLetE <$> mapM dsLetDec decs <*> dsComp rest
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
dsParComp :: [[Stmt]] -> Q (Pat, DExp)
dsParComp [] = return (ConP (tupleDataName 0) [], DConE (tupleDataName 0))
dsParComp (q : rest) = do
  let qv = foldMap extractBoundNamesStmt q
  (rest_pat, rest_exp) <- dsParComp rest
  dsQ <- dsComp (q ++ [mk_tuple_stmt qv])
  let zipped = DAppE (DAppE (DVarE 'mzip) dsQ) rest_exp
  return (ConP (tupleDataName 2) [mk_tuple_pat qv, rest_pat], zipped)

  where
    mk_tuple_stmt :: S.Set Name -> Stmt
    mk_tuple_stmt name_set = 
      NoBindS (foldl AppE (ConE (tupleDataName (S.size name_set)))
                          (S.foldr ((:) . VarE) [] name_set))

    mk_tuple_pat :: S.Set Name -> Pat
    mk_tuple_pat name_set =
      ConP (tupleDataName (S.size name_set)) (S.foldr ((:) . VarP) [] name_set)

-- | Desugar a pattern, returning the desugared pattern and a transformation to
--   be applied to the scope of the pattern match
dsPat :: Pat -> Q (DPat, DExp -> DExp)
dsPat (LitP lit) = return (DLitP lit, id)
dsPat (VarP n) = return (DVarP n, id)
dsPat (TupP pats) = dsConPats (tupleDataName (length pats)) pats
dsPat (UnboxedTupP pats) = dsConPats (unboxedTupleDataName (length pats)) pats
dsPat (ConP name pats) = dsConPats name pats
dsPat (InfixP p1 name p2) = dsConPats name [p1, p2]
dsPat (UInfixP _ _ _) =
  fail "Cannot desugar unresolved infix operators."
dsPat (ParensP pat) = dsPat pat
dsPat (TildeP pat) = dsPatModifier DTildeP pat
dsPat (BangP pat) = dsPatModifier DBangP pat
dsPat (AsP name pat) = do
  (pat', xform) <- dsPat pat
  pat'' <- removeWilds pat'
  let xform' exp = DLetE [DValD (DVarP name) (dPatToDExp pat'')] (xform exp)
  return (pat'', xform')
dsPat WildP = return (DWildP, id)
dsPat (RecP con_name field_pats) = do
  con <- dataConNameToCon con_name
  (reordered, xform) <- case con of
    RecC _name fields -> reorderFieldsPat fields field_pats
    _ -> impossible $ "Record syntax used with non-record constructor "
                      ++ (show con_name) ++ "."
  return (DConP con_name reordered, xform)
dsPat (ListP pats) = go pats
  where go [] = return (DConP '[] [], id)
        go (h : t) = do
          (h', xform_h) <- dsPat h
          (t', xform_t) <- go t
          return (DConP '(:) [h', t'], xform_h . xform_t)
dsPat (SigP pat ty) = do
  (pat', xform) <- dsPat pat
  ty' <- dsType ty
  return (DSigP pat' ty', xform)
dsPat (ViewP _ _) =
  fail "View patterns are not supported in th-desugar. Use pattern guards instead."

-- | Desugar a list of patterns, producing a list of desugared patterns and one
--   transformation (like 'dsPat')
dsPats :: [Pat] -> Q ([DPat], DExp -> DExp)
dsPats pats = do
  (pats', xforms) <- mapAndUnzipM dsPat pats
  return (pats', foldr (.) id xforms)

-- | Desugar patterns that are the arguments to a data constructor
dsConPats :: Name -> [Pat] -> Q (DPat, DExp -> DExp)
dsConPats name pats = do
  (pats', xform) <- dsPats pats
  return (DConP name pats', xform)

-- | Desugar a modified pattern (e.g., body of a @TildeP@)
dsPatModifier :: (DPat -> DPat) -> Pat -> Q (DPat, DExp -> DExp)
dsPatModifier mod pat = do
  (pat', xform) <- dsPat pat
  return (mod pat', xform)

-- | Convert a 'DPat' to a 'DExp'. Fails on 'DWildP'.
dPatToDExp :: DPat -> DExp
dPatToDExp (DLitP lit) = DLitE lit
dPatToDExp (DVarP name) = DVarE name
dPatToDExp (DConP name pats) = foldl DAppE (DConE name) (map dPatToDExp pats)
dPatToDExp (DTildeP pat) = dPatToDExp pat
dPatToDExp (DBangP pat) = dPatToDExp pat
dPatToDExp DWildP = error "Internal error in th-desugar: wildcard in rhs of as-pattern"
dPatToDExp (DSigP pat _) = dPatToDExp pat

-- | Remove all wildcards from a pattern, replacing any wildcard with a fresh
--   variable
removeWilds :: DPat -> Q DPat
removeWilds p@(DLitP _) = return p
removeWilds p@(DVarP _) = return p
removeWilds (DConP con_name pats) = DConP con_name <$> mapM removeWilds pats
removeWilds (DTildeP pat) = DTildeP <$> removeWilds pat
removeWilds (DBangP pat) = DBangP <$> removeWilds pat
removeWilds DWildP = DVarP <$> newName "wild"
removeWilds (DSigP pat ty) = DSigP <$> removeWilds pat <*> pure ty

-- | Desugar @Dec@s that can appear in a let expression
dsLetDec :: Dec -> Q DLetDec
dsLetDec (FunD name clauses) = DFunD name <$> dsClauses name clauses
dsLetDec (ValD pat body where_decs) = do
  (pat', xform) <- dsPat pat
  DValD pat' <$> (xform <$> dsBody body where_decs error_exp)
  where
    error_exp = DAppE (DVarE 'error) (DLitE
                       (StringL $ "Non-exhaustive patterns for " ++ pprint pat))
dsLetDec (SigD name ty) = DSigD name <$> dsType ty
dsLetDec (InfixD fixity name) = return $ DInfixD fixity name
dsLetDec _dec = impossible "Illegal declaration in let expression."

-- | Desugar clauses to a function definition
dsClauses :: Name         -- ^ Name of the function
          -> [Clause]     -- ^ Clauses to desugar
          -> Q [DClause]
dsClauses _ [] = return []
dsClauses n (Clause pats (NormalB exp) where_decs : rest) = do
  -- this is just a convenience optimization; we could tuple up all the patterns
  (pats', xform) <- dsPats pats
  (:) <$>
    DClause pats' <$> (xform <$> (DLetE <$> mapM dsLetDec where_decs <*> dsExp exp)) <*>
    dsClauses n rest
dsClauses n clauses@(Clause pats _ _ : _) = do
  arg_names <- replicateM num_args (newName "arg")
  let scrutinee = foldl DAppE (DConE $ tupleDataName num_args) (map DVarE arg_names)
  clause <- DClause (map DVarP arg_names) <$>
              (DCaseE scrutinee <$> mapM clause_to_dmatch clauses)
  return [clause]
  where
    clause_to_dmatch (Clause pats body where_decs) = do
      (pats', xform) <- dsPats pats
      exp <- dsBody body where_decs error_exp
      return $ DMatch (DConP (tupleDataName num_args) pats') (xform exp)

    num_args = length pats
    error_exp = DAppE (DVarE 'error) (DLitE
                       (StringL $ "Non-exhaustive patterns in " ++ (show n)))

-- | Desugar a type
dsType :: Type -> Q DType
dsType (ForallT tvbs preds ty) = DForallT <$> mapM dsTvb tvbs <*> mapM dsPred preds <*> dsType ty
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

-- | Desugar a @TyVarBndr@
dsTvb :: TyVarBndr -> Q DTyVarBndr
dsTvb (PlainTV n) = return $ DPlainTV n
dsTvb (KindedTV n k) = DKindedTV n <$> dsKind k
#if __GLASGOW_HASKELL__ >= 707
dsTvb (RoledTV n r) = return $ DRoledTV n r
dsTvb (KindedRoledTV n k r) = DKindedRoledTV n <$> dsKind k <*> pure r
#endif

-- | Desugar a @Pred@
dsPred :: Pred -> Q DPred
dsPred (ClassP n tys) = DClassP n <$> mapM dsType tys
dsPred (EqualP t1 t2) = DEqualP <$> dsType t1 <*> dsType t2

-- | Desugar a kind
dsKind :: Kind -> Q DKind
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
                       
-- create a list of expressions in the same order as the fields in the first argument
-- but with the values as given in the second argument
-- if a field is missing from the second argument, use the corresponding expression
-- from the third argument
reorderFields :: [VarStrictType] -> [FieldExp] -> [DExp] -> Q [DExp]
reorderFields [] _ _ = return []
reorderFields ((field_name, _, _) : rest) field_exps (deflt : rest_deflt) = do
  rest' <- reorderFields rest field_exps rest_deflt
  case find (\(exp_name, _) -> exp_name == field_name) field_exps of
    Just (_, exp) -> (: rest') <$> dsExp exp
    Nothing -> return $ deflt : rest'
reorderFields (_ : _) _ [] = impossible "Internal error in th-desugar."

-- like reorderFields, but for patterns, assuming a default of DWildP
reorderFieldsPat :: [VarStrictType] -> [FieldPat] -> Q ([DPat], DExp -> DExp)
reorderFieldsPat [] _ = return ([], id)
reorderFieldsPat ((field_name, _, _) : rest) field_pats = do
  (rest', rest_xform) <- reorderFieldsPat rest field_pats
  case find (\(pat_name, _) -> pat_name == field_name) field_pats of
    Just (_, pat) -> do
      (pat', xform) <- dsPat pat
      return $ (pat' : rest', xform . rest_xform)
    Nothing -> return (DWildP : rest', rest_xform)

