{- Language/Haskell/TH/Desugar/Core.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Desugars full Template Haskell syntax into a smaller core syntax for further
processing. The desugared types and constructors are prefixed with a D.
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, CPP, DeriveDataTypeable,
             DeriveGeneric, TupleSections #-}

module Language.Haskell.TH.Desugar.Core where

import Prelude hiding (mapM, foldl, foldr, all, elem, exp, concatMap, and)

import Language.Haskell.TH hiding (match, clause, cxt)
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.ExpandSyns ( expandSyns )

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Monad hiding (forM_, mapM)
import Control.Monad.Zip
import Control.Monad.Writer hiding (forM_, mapM)
import Data.Foldable hiding (notElem)
import Data.Graph
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Traversable
import Data.Data hiding (Fixity)
#if __GLASGOW_HASKELL__ > 710
import Data.Maybe (isJust)
#endif
import GHC.Generics hiding (Fixity)

#if __GLASGOW_HASKELL__ >= 803
import GHC.OverloadedLabels ( fromLabel )
#endif

import qualified Data.Set as S
import GHC.Exts

import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Reify

-- | Corresponds to TH's @Exp@ type. Note that @DLamE@ takes names, not patterns.
data DExp = DVarE Name
          | DConE Name
          | DLitE Lit
          | DAppE DExp DExp
          | DAppTypeE DExp DType
          | DLamE [Name] DExp
          | DCaseE DExp [DMatch]
          | DLetE [DLetDec] DExp
          | DSigE DExp DType
          | DStaticE DExp
          deriving (Show, Typeable, Data, Generic)


-- | Corresponds to TH's @Pat@ type.
data DPat = DLitPa Lit
          | DVarPa Name
          | DConPa Name [DPat]
          | DTildePa DPat
          | DBangPa DPat
          | DSigPa DPat DType
          | DWildPa
          deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @Type@ type, used to represent
-- types and kinds.
data DType = DForallT [DTyVarBndr] DCxt DType
           | DAppT DType DType
           | DSigT DType DKind
           | DVarT Name
           | DConT Name
           | DArrowT
           | DLitT TyLit
           | DWildCardT
           deriving (Show, Typeable, Data, Generic)

-- | Kinds are types.
type DKind = DType

-- | Corresponds to TH's @Cxt@
type DCxt = [DPred]

-- | Corresponds to TH's @Pred@
data DPred = DAppPr DPred DType
           | DSigPr DPred DKind
           | DVarPr Name
           | DConPr Name
           | DWildCardPr
           deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @TyVarBndr@
data DTyVarBndr = DPlainTV Name
                | DKindedTV Name DKind
                deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @Match@ type.
data DMatch = DMatch DPat DExp
  deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @Clause@ type.
data DClause = DClause [DPat] DExp
  deriving (Show, Typeable, Data, Generic)

-- | Declarations as used in a @let@ statement.
data DLetDec = DFunD Name [DClause]
             | DValD DPat DExp
             | DSigD Name DType
             | DInfixD Fixity Name
             | DPragmaD DPragma
             deriving (Show, Typeable, Data, Generic)

-- | Is it a @newtype@ or a @data@ type?
data NewOrData = Newtype
               | Data
               deriving (Eq, Show, Typeable, Data, Generic)

-- | Corresponds to TH's @Dec@ type.
data DDec = DLetDec DLetDec
          | DDataD NewOrData DCxt Name [DTyVarBndr] (Maybe DKind) [DCon] [DDerivClause]
          | DTySynD Name [DTyVarBndr] DType
          | DClassD DCxt Name [DTyVarBndr] [FunDep] [DDec]
          | DInstanceD (Maybe Overlap) DCxt DType [DDec]
          | DForeignD DForeign
          | DOpenTypeFamilyD DTypeFamilyHead
          | DClosedTypeFamilyD DTypeFamilyHead [DTySynEqn]
          | DDataFamilyD Name [DTyVarBndr] (Maybe DKind)
          | DDataInstD NewOrData DCxt Name [DType] (Maybe DKind) [DCon] [DDerivClause]
          | DTySynInstD Name DTySynEqn
          | DRoleAnnotD Name [Role]
          | DStandaloneDerivD (Maybe DerivStrategy) DCxt DType
          | DDefaultSigD Name DType
          | DPatSynD Name PatSynArgs DPatSynDir DPat
          | DPatSynSigD Name DPatSynType
          deriving (Show, Typeable, Data, Generic)

#if __GLASGOW_HASKELL__ < 711
data Overlap = Overlappable | Overlapping | Overlaps | Incoherent
  deriving (Eq, Ord, Show, Typeable, Data, Generic)
#endif

-- | Corresponds to TH's 'PatSynDir' type
data DPatSynDir = DUnidir              -- ^ @pattern P x {<-} p@
                | DImplBidir           -- ^ @pattern P x {=} p@
                | DExplBidir [DClause] -- ^ @pattern P x {<-} p where P x = e@
                deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's 'PatSynType' type
type DPatSynType = DType

#if __GLASGOW_HASKELL__ < 801
-- | Same as @PatSynArgs@ from TH; defined here for backwards compatibility.
data PatSynArgs
  = PrefixPatSyn [Name]        -- ^ @pattern P {x y z} = p@
  | InfixPatSyn Name Name      -- ^ @pattern {x P y} = p@
  | RecordPatSyn [Name]        -- ^ @pattern P { {x,y,z} } = p@
  deriving (Show, Typeable, Data, Generic)
#endif

-- | Corresponds to TH's 'TypeFamilyHead' type
data DTypeFamilyHead = DTypeFamilyHead Name [DTyVarBndr] DFamilyResultSig
                                       (Maybe InjectivityAnn)
                     deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's 'FamilyResultSig' type
data DFamilyResultSig = DNoSig
                      | DKindSig DKind
                      | DTyVarSig DTyVarBndr
                      deriving (Show, Typeable, Data, Generic)

#if __GLASGOW_HASKELL__ <= 710
data InjectivityAnn = InjectivityAnn Name [Name]
  deriving (Eq, Ord, Show, Typeable, Data, Generic)
#endif

-- | Corresponds to TH's 'Con' type. Unlike 'Con', all 'DCon's reflect GADT
-- syntax. This is beneficial for @th-desugar@'s since it means
-- that all data type declarations can support explicit return kinds, so
-- one does not need to represent them with something like @'Maybe' 'DKind'@,
-- since Haskell98-style data declaration syntax isn't used. Accordingly,
-- there are some differences between 'DCon' and 'Con' to keep in mind:
--
-- * Unlike 'ForallC', where the meaning of the 'TyVarBndr's changes depending
--   on whether it's followed by 'GadtC'/'RecGadtC' or not, the meaning of the
--   'DTyVarBndr's in a 'DCon' is always the same: it is the list of
--   universally /and/ existentially quantified type variables. Note that it is
--   not guaranteed that one set of type variables will appear before the
--   other.
--
-- * A 'DCon' always has an explicit return type.
data DCon = DCon [DTyVarBndr] DCxt Name DConFields
                 DType  -- ^ The GADT result type
          deriving (Show, Typeable, Data, Generic)

-- | A list of fields either for a standard data constructor or a record
-- data constructor.
data DConFields = DNormalC DDeclaredInfix [DBangType]
                | DRecC [DVarBangType]
                deriving (Show, Typeable, Data, Generic)

-- | 'True' if a constructor is declared infix. For normal ADTs, this means
-- that is was written in infix style. For example, both of the constructors
-- below are declared infix.
--
-- @
-- data Infix = Int `Infix` Int | Int :*: Int
-- @
--
-- Whereas neither of these constructors are declared infix:
--
-- @
-- data Prefix = Prefix Int Int | (:+:) Int Int
-- @
--
-- For GADTs, detecting whether a constructor is declared infix is a bit
-- trickier, as one cannot write a GADT constructor "infix-style" like one
-- can for normal ADT constructors. GHC considers a GADT constructor to be
-- declared infix if it meets the following three criteria:
--
-- 1. Its name uses operator syntax (e.g., @(:*:)@).
-- 2. It has exactly two fields (without record syntax).
-- 3. It has a programmer-specified fixity declaration.
--
-- For example, in the following GADT:
--
-- @
-- infixl 5 :**:, :&&:, :^^:, `ActuallyPrefix`
-- data InfixGADT a where
--   (:**:) :: Int -> b -> InfixGADT (Maybe b) -- Only this one is infix
--   ActuallyPrefix :: Char -> Bool -> InfixGADT Double
--   (:&&:) :: { infixGADT1 :: b, infixGADT2 :: Int } -> InfixGADT [b]
--   (:^^:) :: Int -> Int -> Int -> InfixGADT Int
--   (:!!:) :: Char -> Char -> InfixGADT Char
-- @
--
-- Only the @(:**:)@ constructor is declared infix. The other constructors
-- are not declared infix, because:
--
-- * @ActuallyPrefix@ does not use operator syntax (criterion 1).
-- * @(:&&:)@ uses record syntax (criterion 2).
-- * @(:^^:)@ does not have exactly two fields (criterion 2).
-- * @(:!!:)@ does not have a programmer-specified fixity declaration (criterion 3).
type DDeclaredInfix = Bool

-- | Corresponds to TH's @BangType@ type.
type DBangType = (Bang, DType)

-- | Corresponds to TH's @VarBangType@ type.
type DVarBangType = (Name, Bang, DType)

#if __GLASGOW_HASKELL__ <= 710
-- | Corresponds to TH's definition
data SourceUnpackedness = NoSourceUnpackedness
                        | SourceNoUnpack
                        | SourceUnpack
  deriving (Eq, Ord, Show, Typeable, Data, Generic)

-- | Corresponds to TH's definition
data SourceStrictness = NoSourceStrictness
                      | SourceLazy
                      | SourceStrict
  deriving (Eq, Ord, Show, Typeable, Data, Generic)

-- | Corresponds to TH's definition
data Bang = Bang SourceUnpackedness SourceStrictness
  deriving (Eq, Ord, Show, Typeable, Data, Generic)
#endif

-- | Corresponds to TH's @Foreign@ type.
data DForeign = DImportF Callconv Safety String Name DType
              | DExportF Callconv String Name DType
              deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @Pragma@ type.
data DPragma = DInlineP Name Inline RuleMatch Phases
             | DSpecialiseP Name DType (Maybe Inline) Phases
             | DSpecialiseInstP DType
             | DRuleP String [DRuleBndr] DExp DExp Phases
             | DAnnP AnnTarget DExp
             | DLineP Int String
             | DCompleteP [Name] (Maybe Name)
             deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @RuleBndr@ type.
data DRuleBndr = DRuleVar Name
               | DTypedRuleVar Name DType
               deriving (Show, Typeable, Data, Generic)

-- | Corresponds to TH's @TySynEqn@ type (to store type family equations).
data DTySynEqn = DTySynEqn [DType] DType
               deriving (Show, Typeable, Data, Generic)

#if __GLASGOW_HASKELL__ < 707
-- | Same as @Role@ from TH; defined here for GHC 7.6.3 compatibility.
data Role = NominalR | RepresentationalR | PhantomR | InferR
          deriving (Show, Typeable, Data, Generic)

-- | Same as @AnnTarget@ from TH; defined here for GHC 7.6.3 compatibility.
data AnnTarget = ModuleAnnotation
               | TypeAnnotation Name
               | ValueAnnotation Name
               deriving (Show, Typeable, Data, Generic)
#endif

-- | Corresponds to TH's @Info@ type.
data DInfo = DTyConI DDec (Maybe [DInstanceDec])
           | DVarI Name DType (Maybe Name)
               -- ^ The @Maybe Name@ stores the name of the enclosing definition
               -- (datatype, for a data constructor; class, for a method),
               -- if any
           | DTyVarI Name DKind
           | DPrimTyConI Name Int Bool
               -- ^ The @Int@ is the arity; the @Bool@ is whether this tycon
               -- is unlifted.
           | DPatSynI Name DPatSynType
           deriving (Show, Typeable, Data, Generic)

type DInstanceDec = DDec -- ^ Guaranteed to be an instance declaration

-- | Corresponds to TH's @DerivClause@ type.
data DDerivClause = DDerivClause (Maybe DerivStrategy) DCxt
                  deriving (Show, Typeable, Data, Generic)

#if __GLASGOW_HASKELL__ < 801
-- | Same as @DerivStrategy@ from TH; defined here for backwards compatibility.
data DerivStrategy = StockStrategy    -- ^ A \"standard\" derived instance
                   | AnyclassStrategy -- ^ @-XDeriveAnyClass@
                   | NewtypeStrategy  -- ^ @-XGeneralizedNewtypeDeriving@
                   deriving (Show, Typeable, Data, Generic)
#endif

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
    -- the following special case avoids creating a new "let" when it's not
    -- necessary. See #34.
dsExp (CaseE (VarE scrutinee) matches) = do
  matches' <- dsMatches scrutinee matches
  return $ DCaseE (DVarE scrutinee) matches'
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
  reordered <- reorder con
  return $ foldl DAppE (DConE con_name) reordered
  where
    reorder con = case con of
                    NormalC _name fields -> non_record fields
                    InfixC field1 _name field2 -> non_record [field1, field2]
                    RecC _name fields -> reorder_fields fields
                    ForallC _ _ c -> reorder c
#if __GLASGOW_HASKELL__ >= 800
                    GadtC _names fields _ret_ty -> non_record fields
                    RecGadtC _names fields _ret_ty -> reorder_fields fields
#endif

    reorder_fields fields = reorderFields con_name fields field_exps
                                          (repeat $ DVarE 'undefined)

    non_record fields | null field_exps
                        -- Special case: record construction is allowed for any
                        -- constructor, regardless of whether the constructor
                        -- actually was declared with records, provided that no
                        -- records are given in the expression itself. (See #59).
                        --
                        -- Con{} desugars down to Con undefined ... undefined.
                      = return $ replicate (length fields) $ DVarE 'undefined

                      | otherwise =
                          impossible $ "Record syntax used with non-record constructor "
                                       ++ (show con_name) ++ "."

dsExp (RecUpdE exp field_exps) = do
  -- here, we need to use one of the field names to find the tycon, somewhat dodgily
  first_name <- case field_exps of
                  ((name, _) : _) -> return name
                  _ -> impossible "Record update with no fields listed."
  info <- reifyWithLocals first_name
  applied_type <- case info of
#if __GLASGOW_HASKELL__ > 710
                    VarI _name ty _m_dec -> extract_first_arg ty
#else
                    VarI _name ty _m_dec _fixity -> extract_first_arg ty
#endif
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
        args_contain_names args =
          let con_field_names = map fst_of_3 args in
          all (`elem` con_field_names) field_names

        has_names (RecC _con_name args) =
          args_contain_names args
#if __GLASGOW_HASKELL__ >= 800
        has_names (RecGadtC _con_name args _ret_ty) =
          args_contain_names args
#endif
        has_names (ForallC _ _ c) = has_names c
        has_names _               = False

    rec_con_to_dmatch con_name args = do
      let con_field_names = map fst_of_3 args
      field_var_names <- mapM (newUniqueName . nameBase) con_field_names
      DMatch (DConPa con_name (map DVarPa field_var_names)) <$>
             (foldl DAppE (DConE con_name) <$>
                    (reorderFields con_name args field_exps (map DVarE field_var_names)))

    con_to_dmatch :: DsMonad q => Con -> q DMatch
    con_to_dmatch (RecC con_name args) = rec_con_to_dmatch con_name args
#if __GLASGOW_HASKELL__ >= 800
    -- We're assuming the GADT constructor has only one Name here, but since
    -- this constructor was reified, this assumption should always hold true.
    con_to_dmatch (RecGadtC [con_name] args _ret_ty) = rec_con_to_dmatch con_name args
#endif
    con_to_dmatch (ForallC _ _ c) = con_to_dmatch c
    con_to_dmatch _ = impossible "Internal error within th-desugar."

    error_match = DMatch DWildPa (DAppE (DVarE 'error)
                   (DLitE (StringL "Non-exhaustive patterns in record update")))

    fst_of_3 (x, _, _) = x
#if __GLASGOW_HASKELL__ >= 709
dsExp (StaticE exp) = DStaticE <$> dsExp exp
#endif
#if __GLASGOW_HASKELL__ > 710
dsExp (UnboundVarE n) = return (DVarE n)
#endif
#if __GLASGOW_HASKELL__ >= 801
dsExp (AppTypeE exp ty) = DAppTypeE <$> dsExp exp <*> dsType ty
dsExp (UnboxedSumE exp alt arity) =
  DAppE (DConE $ unboxedSumDataName alt arity) <$> dsExp exp
#endif
#if __GLASGOW_HASKELL__ >= 803
dsExp (LabelE str) = return $ DVarE 'fromLabel `DAppTypeE` DLitT (StrTyLit str)
#endif

-- | Desugar a lambda expression, where the body has already been desugared
dsLam :: DsMonad q => [Pat] -> DExp -> q DExp
dsLam = mkLam stripVarP_maybe dsPatsOverExp

-- | Convert a list of 'DPat' arguments and a 'DExp' body into a 'DLamE'. This
-- is needed since 'DLamE' takes a list of 'Name's for its bound variables
-- instead of 'DPat's, so some reorganization is needed.
mkDLamEFromDPats :: DsMonad q => [DPat] -> DExp -> q DExp
mkDLamEFromDPats = mkLam stripDVarPa_maybe (\pats exp -> return (pats, exp))
  where
    stripDVarPa_maybe :: DPat -> Maybe Name
    stripDVarPa_maybe (DVarPa n) = Just n
    stripDVarPa_maybe _          = Nothing

-- | Generalizes 'dsLam' and 'mkDLamEFromDPats' to work over an arbitrary
-- pattern type.
mkLam :: DsMonad q
      => (pat -> Maybe Name) -- ^ Should return @'Just' n@ if the argument is a
                             --   variable pattern, and 'Nothing' otherwise.
      -> ([pat] -> DExp -> q ([DPat], DExp))
                             -- ^ Should process a list of @pat@ arguments and
                             --   a 'DExp' body. (This might do some internal
                             --   reorganization if there are as-patterns, as
                             --   in the case of 'dsPatsOverExp'.)
      -> [pat] -> DExp -> q DExp
mkLam mb_strip_var_pat process_pats_over_exp pats exp
  | Just names <- mapM mb_strip_var_pat pats
  = return $ DLamE names exp
  | otherwise
  = do arg_names <- replicateM (length pats) (newUniqueName "arg")
       let scrutinee = mkTupleDExp (map DVarE arg_names)
       (pats', exp') <- process_pats_over_exp pats exp
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
  reordered <- reorder con
  return $ DConPa con_name reordered
  where
    reorder con = case con of
                     NormalC _name fields -> non_record fields
                     InfixC field1 _name field2 -> non_record [field1, field2]
                     RecC _name fields -> reorder_fields_pat fields
                     ForallC _ _ c -> reorder c
#if __GLASGOW_HASKELL__ >= 800
                     GadtC _names fields _ret_ty -> non_record fields
                     RecGadtC _names fields _ret_ty -> reorder_fields_pat fields
#endif

    reorder_fields_pat fields = reorderFieldsPat con_name fields field_pats

    non_record fields | null field_pats
                        -- Special case: record patterns are allowed for any
                        -- constructor, regardless of whether the constructor
                        -- actually was declared with records, provided that
                        -- no records are given in the pattern itself. (See #59).
                        --
                        -- Con{} desugars down to Con _ ... _.
                      = return $ replicate (length fields) DWildPa
                      | otherwise = lift $ impossible
                                         $ "Record syntax used with non-record constructor "
                                           ++ (show con_name) ++ "."

dsPat (ListP pats) = go pats
  where go [] = return $ DConPa '[] []
        go (h : t) = do
          h' <- dsPat h
          t' <- go t
          return $ DConPa '(:) [h', t']
dsPat (SigP pat ty) = DSigPa <$> dsPat pat <*> dsType ty
#if __GLASGOW_HASKELL__ >= 801
dsPat (UnboxedSumP pat alt arity) =
  DConPa (unboxedSumDataName alt arity) <$> ((:[]) <$> dsPat pat)
#endif
dsPat (ViewP _ _) =
  fail "View patterns are not supported in th-desugar. Use pattern guards instead."

-- | Convert a 'DPat' to a 'DExp'. Fails on 'DWildP'.
dPatToDExp :: DPat -> DExp
dPatToDExp (DLitPa lit) = DLitE lit
dPatToDExp (DVarPa name) = DVarE name
dPatToDExp (DConPa name pats) = foldl DAppE (DConE name) (map dPatToDExp pats)
dPatToDExp (DTildePa pat) = dPatToDExp pat
dPatToDExp (DBangPa pat) = dPatToDExp pat
dPatToDExp (DSigPa pat ty) = DSigE (dPatToDExp pat) ty
dPatToDExp DWildPa = error "Internal error in th-desugar: wildcard in rhs of as-pattern"

-- | Remove all wildcards from a pattern, replacing any wildcard with a fresh
--   variable
removeWilds :: DsMonad q => DPat -> q DPat
removeWilds p@(DLitPa _) = return p
removeWilds p@(DVarPa _) = return p
removeWilds (DConPa con_name pats) = DConPa con_name <$> mapM removeWilds pats
removeWilds (DTildePa pat) = DTildePa <$> removeWilds pat
removeWilds (DBangPa pat) = DBangPa <$> removeWilds pat
removeWilds (DSigPa pat ty) = DSigPa <$> removeWilds pat <*> pure ty
removeWilds DWildPa = DVarPa <$> newUniqueName "wild"

extractBoundNamesDPat :: DPat -> S.Set Name
extractBoundNamesDPat (DLitPa _)      = S.empty
extractBoundNamesDPat (DVarPa n)      = S.singleton n
extractBoundNamesDPat (DConPa _ pats) = S.unions (map extractBoundNamesDPat pats)
extractBoundNamesDPat (DTildePa p)    = extractBoundNamesDPat p
extractBoundNamesDPat (DBangPa p)     = extractBoundNamesDPat p
extractBoundNamesDPat (DSigPa p _)    = extractBoundNamesDPat p
extractBoundNamesDPat DWildPa         = S.empty

-- | Desugar @Info@
dsInfo :: DsMonad q => Info -> q DInfo
dsInfo (ClassI dec instances) = do
  [ddec]     <- dsDec dec
  dinstances <- dsDecs instances
  return $ DTyConI ddec (Just dinstances)
#if __GLASGOW_HASKELL__ > 710
dsInfo (ClassOpI name ty parent) =
#else
dsInfo (ClassOpI name ty parent _fixity) =
#endif
  DVarI name <$> dsType ty <*> pure (Just parent)
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
#if __GLASGOW_HASKELL__ > 710
dsInfo (DataConI name ty parent) =
  DVarI name <$> dsType ty <*> pure (Just parent)
dsInfo (VarI name ty Nothing) =
  DVarI name <$> dsType ty <*> pure Nothing
dsInfo (VarI name _ (Just _)) =
  impossible $ "Declaration supplied with variable: " ++ show name
#else
dsInfo (DataConI name ty parent _fixity) =
  DVarI name <$> dsType ty <*> pure (Just parent)
dsInfo (VarI name ty Nothing _fixity) =
  DVarI name <$> dsType ty <*> pure Nothing
dsInfo (VarI name _ (Just _) _) =
  impossible $ "Declaration supplied with variable: " ++ show name
#endif
dsInfo (TyVarI name ty) = DTyVarI name <$> dsType ty
#if __GLASGOW_HASKELL__ >= 801
dsInfo (PatSynI name ty) = DPatSynI name <$> dsType ty
#endif

fixBug8884ForFamilies :: DsMonad q => DDec -> q (DDec, Int)
#if __GLASGOW_HASKELL__ < 708
fixBug8884ForFamilies (DOpenTypeFamilyD (DTypeFamilyHead name tvbs frs ann)) = do
  let num_args = length tvbs
  frs' <- remove_arrows num_args frs
  return (DOpenTypeFamilyD (DTypeFamilyHead name tvbs frs' ann),num_args)
fixBug8884ForFamilies (DClosedTypeFamilyD (DTypeFamilyHead name tvbs frs ann) eqns) = do
  let num_args = length tvbs
      eqns' = map (fixBug8884ForEqn num_args) eqns
  frs' <- remove_arrows num_args frs
  return (DClosedTypeFamilyD (DTypeFamilyHead name tvbs frs' ann) eqns', num_args)
fixBug8884ForFamilies dec@(DDataFamilyD _ _ _)
  = return (dec, 0)   -- the num_args is ignored for data families
fixBug8884ForFamilies dec =
  impossible $ "Reifying yielded a FamilyI with a non-family Dec: " ++ show dec

remove_arrows :: DsMonad q => Int -> DFamilyResultSig -> q DFamilyResultSig
remove_arrows n (DKindSig k) = DKindSig <$> remove_arrows_kind n k
remove_arrows n (DTyVarSig (DKindedTV nm k)) =
  DTyVarSig <$> (DKindedTV nm <$> remove_arrows_kind n k)
remove_arrows _ frs = return frs

remove_arrows_kind :: DsMonad q => Int -> DKind -> q DKind
remove_arrows_kind 0 k = return k
remove_arrows_kind n (DAppT (DAppT DArrowT _) k) = remove_arrows_kind (n-1) k
remove_arrows_kind _ _ =
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
#if __GLASGOW_HASKELL__ > 710
dsDec (DataD cxt n tvbs mk cons derivings) = do
  tvbs'    <- mapM dsTvb tvbs
  all_tvbs <- nonFamilyDataTvbs tvbs' mk
  let data_type = nonFamilyDataReturnType n all_tvbs
  (:[]) <$> (DDataD Data <$> dsCxt cxt <*> pure n
                         <*> pure tvbs' <*> mapM dsType mk
                         <*> concatMapM (dsCon tvbs' data_type) cons
                         <*> mapM dsDerivClause derivings)
dsDec (NewtypeD cxt n tvbs mk con derivings) = do
  tvbs'    <- mapM dsTvb tvbs
  all_tvbs <- nonFamilyDataTvbs tvbs' mk
  let data_type = nonFamilyDataReturnType n all_tvbs
  (:[]) <$> (DDataD Newtype <$> dsCxt cxt <*> pure n
                            <*> pure tvbs' <*> mapM dsType mk
                            <*> dsCon tvbs' data_type con
                            <*> mapM dsDerivClause derivings)
#else
dsDec (DataD cxt n tvbs cons derivings) = do
  tvbs' <- mapM dsTvb tvbs
  let data_type = nonFamilyDataReturnType n tvbs'
  (:[]) <$> (DDataD Data <$> dsCxt cxt <*> pure n
                         <*> pure tvbs' <*> pure Nothing
                         <*> concatMapM (dsCon tvbs' data_type) cons
                         <*> mapM dsDerivClause derivings)
dsDec (NewtypeD cxt n tvbs con derivings) = do
  tvbs' <- mapM dsTvb tvbs
  let data_type = nonFamilyDataReturnType n tvbs'
  (:[]) <$> (DDataD Newtype <$> dsCxt cxt <*> pure n
                            <*> pure tvbs' <*> pure Nothing
                            <*> dsCon tvbs' data_type con
                            <*> mapM dsDerivClause derivings)
#endif
dsDec (TySynD n tvbs ty) =
  (:[]) <$> (DTySynD n <$> mapM dsTvb tvbs <*> dsType ty)
dsDec (ClassD cxt n tvbs fds decs) =
  (:[]) <$> (DClassD <$> dsCxt cxt <*> pure n <*> mapM dsTvb tvbs
                     <*> pure fds <*> dsDecs decs)
#if __GLASGOW_HASKELL__ >= 711
dsDec (InstanceD over cxt ty decs) =
  (:[]) <$> (DInstanceD <$> pure over <*> dsCxt cxt <*> dsType ty <*> dsDecs decs)
#else
dsDec (InstanceD cxt ty decs) =
  (:[]) <$> (DInstanceD <$> pure Nothing <*> dsCxt cxt <*> dsType ty <*> dsDecs decs)
#endif
dsDec d@(SigD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec (ForeignD f) = (:[]) <$> (DForeignD <$> dsForeign f)
dsDec d@(InfixD {}) = (fmap . map) DLetDec $ dsLetDec d
dsDec d@(PragmaD {}) = (fmap . map) DLetDec $ dsLetDec d
#if __GLASGOW_HASKELL__ > 710
dsDec (OpenTypeFamilyD tfHead) =
  (:[]) <$> (DOpenTypeFamilyD <$> dsTypeFamilyHead tfHead)
dsDec (DataFamilyD n tvbs m_k) =
  (:[]) <$> (DDataFamilyD n <$> mapM dsTvb tvbs <*> mapM dsType m_k)
#else
dsDec (FamilyD TypeFam n tvbs m_k) = do
  (:[]) <$> (DOpenTypeFamilyD <$> dsTypeFamilyHead n tvbs m_k)
dsDec (FamilyD DataFam n tvbs m_k) =
  (:[]) <$> (DDataFamilyD n <$> mapM dsTvb tvbs <*> mapM dsType m_k)
#endif
#if __GLASGOW_HASKELL__ > 710
dsDec (DataInstD cxt n tys mk cons derivings) = do
  tys'    <- mapM dsType tys
  all_tys <- dataFamInstTypes tys' mk
  let tvbs = dataFamInstTvbs all_tys
      fam_inst_type = dataFamInstReturnType n all_tys
  (:[]) <$> (DDataInstD Data <$> dsCxt cxt <*> pure n
                             <*> pure tys' <*> mapM dsType mk
                             <*> concatMapM (dsCon tvbs fam_inst_type) cons
                             <*> mapM dsDerivClause derivings)
dsDec (NewtypeInstD cxt n tys mk con derivings) = do
  tys'    <- mapM dsType tys
  all_tys <- dataFamInstTypes tys' mk
  let tvbs = dataFamInstTvbs all_tys
      fam_inst_type = dataFamInstReturnType n all_tys
  (:[]) <$> (DDataInstD Newtype <$> dsCxt cxt <*> pure n
                                <*> pure tys' <*> mapM dsType mk
                                <*> dsCon tvbs fam_inst_type con
                                <*> mapM dsDerivClause derivings)
#else
dsDec (DataInstD cxt n tys cons derivings) = do
  tys' <- mapM dsType tys
  let tvbs = dataFamInstTvbs tys'
      fam_inst_type = dataFamInstReturnType n tys'
  (:[]) <$> (DDataInstD Data <$> dsCxt cxt <*> pure n
                             <*> pure tys' <*> pure Nothing
                             <*> concatMapM (dsCon tvbs fam_inst_type) cons
                             <*> mapM dsDerivClause derivings)
dsDec (NewtypeInstD cxt n tys con derivings) = do
  tys' <- mapM dsType tys
  let tvbs = dataFamInstTvbs tys'
      fam_inst_type = dataFamInstReturnType n tys'
  (:[]) <$> (DDataInstD Newtype <$> dsCxt cxt <*> pure n
                                <*> pure tys' <*> pure Nothing
                                <*> dsCon tvbs fam_inst_type con
                                <*> mapM dsDerivClause derivings)
#endif
#if __GLASGOW_HASKELL__ < 707
dsDec (TySynInstD n lhs rhs) = (:[]) <$> (DTySynInstD n <$>
                                          (DTySynEqn <$> mapM dsType lhs
                                                     <*> dsType rhs))
#else
dsDec (TySynInstD n eqn) = (:[]) <$> (DTySynInstD n <$> dsTySynEqn eqn)
#if __GLASGOW_HASKELL__ > 710
dsDec (ClosedTypeFamilyD tfHead eqns) =
  (:[]) <$> (DClosedTypeFamilyD <$> dsTypeFamilyHead tfHead
                                <*> mapM dsTySynEqn eqns)
#else
dsDec (ClosedTypeFamilyD n tvbs m_k eqns) = do
  (:[]) <$> (DClosedTypeFamilyD <$> dsTypeFamilyHead n tvbs m_k
                                <*> mapM dsTySynEqn eqns)
#endif
dsDec (RoleAnnotD n roles) = return [DRoleAnnotD n roles]
#endif
#if __GLASGOW_HASKELL__ >= 709
#if __GLASGOW_HASKELL__ >= 801
dsDec (PatSynD n args dir pat) = do
  dir' <- dsPatSynDir n dir
  (pat', vars) <- dsPatX pat
  unless (null vars) $
    fail $ "Pattern synonym definition cannot contain as-patterns (@)."
  return [DPatSynD n args dir' pat']
dsDec (PatSynSigD n ty) = (:[]) <$> (DPatSynSigD n <$> dsType ty)
dsDec (StandaloneDerivD mds cxt ty) =
  (:[]) <$> (DStandaloneDerivD mds     <$> dsCxt cxt <*> dsType ty)
#else
dsDec (StandaloneDerivD cxt ty) =
  (:[]) <$> (DStandaloneDerivD Nothing <$> dsCxt cxt <*> dsType ty)
#endif
dsDec (DefaultSigD n ty) = (:[]) <$> (DDefaultSigD n <$> dsType ty)
#endif

-- Like mkExtraDKindBinders, but accepts a Maybe Kind
-- argument instead of DKind.
mkExtraKindBinders :: DsMonad q => Maybe Kind -> q [DTyVarBndr]
mkExtraKindBinders =
  maybe (pure (DConT typeKindName)) (runQ . expandSyns >=> dsType) >=> mkExtraDKindBinders'

-- | Like mkExtraDKindBinders, but assumes kind synonyms have been expanded.
mkExtraDKindBinders' :: Quasi q => DKind -> q [DTyVarBndr]
mkExtraDKindBinders' k = do
  let (_, _, args, _) = unravel k
  names <- replicateM (length args) (qNewName "a")
  return (zipWith DKindedTV names args)

#if __GLASGOW_HASKELL__ > 710
-- | Desugar a @FamilyResultSig@
dsFamilyResultSig :: DsMonad q => FamilyResultSig -> q DFamilyResultSig
dsFamilyResultSig NoSig          = return DNoSig
dsFamilyResultSig (KindSig k)    = DKindSig <$> dsType k
dsFamilyResultSig (TyVarSig tvb) = DTyVarSig <$> dsTvb tvb

-- | Desugar a @TypeFamilyHead@
dsTypeFamilyHead :: DsMonad q => TypeFamilyHead -> q DTypeFamilyHead
dsTypeFamilyHead (TypeFamilyHead n tvbs result inj)
  = DTypeFamilyHead n <$> mapM dsTvb tvbs
                      <*> dsFamilyResultSig result
                      <*> pure inj
#else
-- | Desugar bits and pieces into a 'DTypeFamilyHead'
dsTypeFamilyHead :: DsMonad q
                 => Name -> [TyVarBndr] -> Maybe Kind -> q DTypeFamilyHead
dsTypeFamilyHead n tvbs m_kind = do
  result_sig <- case m_kind of
    Nothing -> return DNoSig
    Just k  -> DKindSig <$> dsType k
  DTypeFamilyHead n <$> mapM dsTvb tvbs
                    <*> pure result_sig
                    <*> pure Nothing
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
dsLetDec (PragmaD prag) = (:[]) <$> (DPragmaD <$> dsPragma prag)
dsLetDec _dec = impossible "Illegal declaration in let expression."

-- | Desugar a single @Con@.
--
-- Because we always desugar @Con@s to GADT syntax (see the documentation for
-- 'DCon'), it is not always possible to desugar with just a 'Con' alone.
-- For instance, we must desugar:
--
-- @
-- data Foo a = forall b. MkFoo b
-- @
--
-- To this:
--
-- @
-- data Foo a :: Type where
--   MkFoo :: forall a b. b -> Foo a
-- @
--
-- If our only argument was @forall b. MkFoo b@, it would be somewhat awkward
-- to figure out (1) what the set of universally quantified type variables
-- (@[a]@) was, and (2) what the return type (@Foo a@) was. For this reason,
-- we require passing these as arguments. (If we desugar an actual GADT
-- constructor, these arguments are ignored.)
dsCon :: DsMonad q
      => [DTyVarBndr] -- ^ The universally quantified type variables
                      --   (used if desugaring a non-GADT constructor).
      -> DType        -- ^ The original data declaration's type
                      --   (used if desugaring a non-GADT constructor).
      -> Con -> q [DCon]
dsCon univ_dtvbs data_type con = do
  dcons' <- dsCon' con
  return $ flip map dcons' $ \(n, dtvbs, dcxt, fields, m_gadt_type) ->
    case m_gadt_type of
      Nothing ->
        let ex_dtvbs = dtvbs in
        DCon (univ_dtvbs ++ ex_dtvbs) dcxt n fields data_type
      Just gadt_type ->
        let univ_ex_dtvbs = dtvbs in
        DCon univ_ex_dtvbs dcxt n fields gadt_type

-- Desugar a Con in isolation. The meaning of the returned DTyVarBndrs changes
-- depending on what the returned Maybe DType value is:
--
-- * If returning Just gadt_ty, then we've encountered a GadtC or RecGadtC,
--   so the returned DTyVarBndrs are both the universally and existentially
--   quantified tyvars.
-- * If returning Nothing, we're dealing with a non-GADT constructor, so
--   the returned DTyVarBndrs are the existentials only.
dsCon' :: DsMonad q
       => Con -> q [(Name, [DTyVarBndr], DCxt, DConFields, Maybe DType)]
dsCon' (NormalC n stys) = do
  dtys <- mapM dsBangType stys
  return [(n, [], [], DNormalC False dtys, Nothing)]
dsCon' (RecC n vstys) = do
  vdtys <- mapM dsVarBangType vstys
  return [(n, [], [], DRecC vdtys, Nothing)]
dsCon' (InfixC sty1 n sty2) = do
  dty1 <- dsBangType sty1
  dty2 <- dsBangType sty2
  return [(n, [], [], DNormalC True [dty1, dty2], Nothing)]
dsCon' (ForallC tvbs cxt con) = do
  dtvbs <- mapM dsTvb tvbs
  dcxt <- dsCxt cxt
  dcons' <- dsCon' con
  return $ flip map dcons' $ \(n, dtvbs', dcxt', fields, m_gadt_type) ->
    (n, dtvbs ++ dtvbs', dcxt ++ dcxt', fields, m_gadt_type)
#if __GLASGOW_HASKELL__ > 710
dsCon' (GadtC nms btys rty) = do
  dbtys <- mapM dsBangType btys
  drty  <- dsType rty
  sequence $ flip map nms $ \nm -> do
    mbFi <- reifyFixityWithLocals nm
    -- A GADT data constructor is declared infix when these three
    -- properties hold:
    let decInfix = isInfixDataCon (nameBase nm) -- 1. Its name uses operator syntax
                                                --    (e.g., (:*:))
                || length dbtys == 2            -- 2. It has exactly two fields
                || isJust mbFi                  -- 3. It has a programmer-specified
                                                --    fixity declaration
    return (nm, [], [], DNormalC decInfix dbtys, Just drty)
dsCon' (RecGadtC nms vbtys rty) = do
  dvbtys <- mapM dsVarBangType vbtys
  drty   <- dsType rty
  return $ flip map nms $ \nm ->
    (nm, [], [], DRecC dvbtys, Just drty)
#endif

#if __GLASGOW_HASKELL__ > 710
-- | Desugar a @BangType@ (or a @StrictType@, if you're old-fashioned)
dsBangType :: DsMonad q => BangType -> q DBangType
dsBangType (b, ty) = (b, ) <$> dsType ty

-- | Desugar a @VarBangType@ (or a @VarStrictType@, if you're old-fashioned)
dsVarBangType :: DsMonad q => VarBangType -> q DVarBangType
dsVarBangType (n, b, ty) = (n, b, ) <$> dsType ty
#else
-- | Desugar a @BangType@ (or a @StrictType@, if you're old-fashioned)
dsBangType :: DsMonad q => StrictType -> q DBangType
dsBangType (b, ty) = (strictToBang b, ) <$> dsType ty

-- | Desugar a @VarBangType@ (or a @VarStrictType@, if you're old-fashioned)
dsVarBangType :: DsMonad q => VarStrictType -> q DVarBangType
dsVarBangType (n, b, ty) = (n, strictToBang b, ) <$> dsType ty
#endif

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
#if __GLASGOW_HASKELL__ >= 709
dsPragma (LineP n str)                   = return $ DLineP n str
#endif
#if __GLASGOW_HASKELL__ >= 801
dsPragma (CompleteP cls mty)             = return $ DCompleteP cls mty
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
  -- this case is necessary to maintain the roundtrip property.
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
dsType (SigT ty ki) = DSigT <$> dsType ty <*> dsType ki
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
dsType StarT = return $ DConT typeKindName
dsType ConstraintT = return $ DConT ''Constraint
dsType (LitT lit) = return $ DLitT lit
#if __GLASGOW_HASKELL__ >= 709
dsType EqualityT = return $ DConT ''(~)
#endif
#if __GLASGOW_HASKELL__ > 710
dsType (InfixT t1 n t2) = DAppT <$> (DAppT (DConT n) <$> dsType t1) <*> dsType t2
dsType (UInfixT _ _ _) = fail "Cannot desugar unresolved infix operators."
dsType (ParensT t) = dsType t
dsType WildCardT = return DWildCardT
#endif
#if __GLASGOW_HASKELL__ >= 801
dsType (UnboxedSumT arity) = return $ DConT (unboxedSumTypeName arity)
#endif

-- | Desugar a @TyVarBndr@
dsTvb :: DsMonad q => TyVarBndr -> q DTyVarBndr
dsTvb (PlainTV n) = return $ DPlainTV n
dsTvb (KindedTV n k) = DKindedTV n <$> dsType k

-- | Desugar a @Cxt@
dsCxt :: DsMonad q => Cxt -> q DCxt
dsCxt = concatMapM dsPred

#if __GLASGOW_HASKELL__ >= 801
-- | Desugar a @DerivClause@.
dsDerivClause :: DsMonad q => DerivClause -> q DDerivClause
dsDerivClause (DerivClause mds cxt) = DDerivClause mds <$> dsCxt cxt
#elif __GLASGOW_HASKELL__ >= 711
dsDerivClause :: DsMonad q => Pred -> q DDerivClause
dsDerivClause p = DDerivClause Nothing <$> dsPred p
#else
dsDerivClause :: DsMonad q => Name -> q DDerivClause
dsDerivClause n = pure $ DDerivClause Nothing [DConPr n]
#endif

#if __GLASGOW_HASKELL__ >= 801
-- | Desugar a @PatSynDir@. (Available only with GHC 8.2+)
dsPatSynDir :: DsMonad q => Name -> PatSynDir -> q DPatSynDir
dsPatSynDir _ Unidir              = pure DUnidir
dsPatSynDir _ ImplBidir           = pure DImplBidir
dsPatSynDir n (ExplBidir clauses) = DExplBidir <$> dsClauses n clauses
#endif

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
    [p]   -> (:[]) <$> DSigPr p <$> dsType ki
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
#if __GLASGOW_HASKELL__ > 710
dsPred (InfixT t1 n t2) = (:[]) <$> (DAppPr <$> (DAppPr (DConPr n) <$> dsType t1) <*> dsType t2)
dsPred (UInfixT _ _ _) = fail "Cannot desugar unresolved infix operators."
dsPred (ParensT t) = dsPred t
dsPred WildCardT = return [DWildCardPr]
#endif
#if __GLASGOW_HASKELL__ >= 801
dsPred t@(UnboxedSumT {}) =
  impossible $ "Unboxed sum seen as head of constraint: " ++ show t
#endif
#endif

-- | Like 'reify', but safer and desugared. Uses local declarations where
-- available.
dsReify :: DsMonad q => Name -> q (Maybe DInfo)
dsReify = traverse dsInfo <=< reifyWithLocals_maybe

-- create a list of expressions in the same order as the fields in the first argument
-- but with the values as given in the second argument
-- if a field is missing from the second argument, use the corresponding expression
-- from the third argument
reorderFields :: DsMonad q => Name -> [VarStrictType] -> [FieldExp] -> [DExp] -> q [DExp]
reorderFields = reorderFields' dsExp

reorderFieldsPat :: DsMonad q => Name -> [VarStrictType] -> [FieldPat] -> PatM q [DPat]
reorderFieldsPat con_name field_decs field_pats =
  reorderFields' dsPat con_name field_decs field_pats (repeat DWildPa)

reorderFields' :: (Applicative m, Monad m)
               => (a -> m da)
               -> Name -- ^ The name of the constructor (used for error reporting)
               -> [VarStrictType] -> [(Name, a)]
               -> [da] -> m [da]
reorderFields' ds_thing con_name field_names_types field_things deflts =
  check_valid_fields >> reorder field_names deflts
  where
    field_names = map (\(a, _, _) -> a) field_names_types

    check_valid_fields =
      forM_ field_things $ \(thing_name, _) ->
        unless (thing_name `elem` field_names) $
          fail $ "Constructor ‘" ++ nameBase con_name   ++ "‘ does not have field ‘"
                                 ++ nameBase thing_name ++ "‘"

    reorder [] _ = return []
    reorder (field_name : rest) (deflt : rest_deflt) = do
      rest' <- reorder rest rest_deflt
      case find (\(thing_name, _) -> thing_name == field_name) field_things of
        Just (_, thing) -> (: rest') <$> ds_thing thing
        Nothing -> return $ deflt : rest'
    reorder (_ : _) [] = error "Internal error in th-desugar."

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
isUniversalPattern (DTildePa {})  = return True
isUniversalPattern (DBangPa pat)  = isUniversalPattern pat
isUniversalPattern (DSigPa pat _) = isUniversalPattern pat
isUniversalPattern DWildPa        = return True

-- | Apply one 'DExp' to a list of arguments
applyDExp :: DExp -> [DExp] -> DExp
applyDExp = foldl DAppE

-- | Apply one 'DType' to a list of arguments
applyDType :: DType -> [DType] -> DType
applyDType = foldl DAppT

-- | Convert a 'DTyVarBndr' into a 'DType'
dTyVarBndrToDType :: DTyVarBndr -> DType
dTyVarBndrToDType (DPlainTV a)    = DVarT a
dTyVarBndrToDType (DKindedTV a k) = DVarT a `DSigT` k

-- | Convert a 'Strict' to a 'Bang' in GHCs 7.x. This is just
-- the identity operation in GHC 8.x, which has no 'Strict'.
-- (This is included in GHC 8.x only for good Haddocking.)
#if __GLASGOW_HASKELL__ <= 710
strictToBang :: Strict -> Bang
strictToBang IsStrict  = Bang NoSourceUnpackedness SourceStrict
strictToBang NotStrict = Bang NoSourceUnpackedness NoSourceStrictness
strictToBang Unpacked  = Bang SourceUnpack SourceStrict
#else
strictToBang :: Bang -> Bang
strictToBang = id
#endif

-- | Convert a 'DType' to a 'DPred'
dTypeToDPred :: Monad q => DType -> q DPred
dTypeToDPred (DForallT _ _ _) = impossible "Forall-type used as constraint"
dTypeToDPred (DAppT t1 t2)   = liftM2 DAppPr (dTypeToDPred t1) (return t2)
dTypeToDPred (DSigT ty ki)   = liftM2 DSigPr (dTypeToDPred ty) (return ki)
dTypeToDPred (DVarT n)       = return $ DVarPr n
dTypeToDPred (DConT n)       = return $ DConPr n
dTypeToDPred DArrowT         = impossible "Arrow used as head of constraint"
dTypeToDPred (DLitT _)       = impossible "Type literal used as head of constraint"
dTypeToDPred DWildCardT      = return DWildCardPr

-- Take a data type name (which does not belong to a data family) and
-- apply it to its type variable binders to form a DType.
nonFamilyDataReturnType :: Name -> [DTyVarBndr] -> DType
nonFamilyDataReturnType con_name = applyDType (DConT con_name) . map dTyVarBndrToDType

-- Take a data family name and apply it to its argument types to form a
-- data family instance DType.
dataFamInstReturnType :: Name -> [DType] -> DType
dataFamInstReturnType fam_name = applyDType (DConT fam_name)

-- Take a data type (which does not belong to a data family) of the form
-- @Foo a :: k -> Type -> Type@ and return @Foo a (b :: k) (c :: Type)@, where
-- @b@ and @c@ are fresh type variable names.
nonFamilyDataTvbs :: DsMonad q => [DTyVarBndr] -> Maybe Kind -> q [DTyVarBndr]
nonFamilyDataTvbs tvbs mk = do
  extra_tvbs <- mkExtraKindBinders mk
  pure $ tvbs ++ extra_tvbs

-- Take a data family instance of the form @Foo a :: k -> Type -> Type@ and
-- return @Foo a (b :: k) (c :: Type)@, where @b@ and @c@ are fresh type
-- variable names.
dataFamInstTypes :: DsMonad q => [DType] -> Maybe Kind -> q [DType]
dataFamInstTypes tys mk = do
  extra_tvbs <- mkExtraKindBinders mk
  pure $ tys ++ map dTyVarBndrToDType extra_tvbs

-- Unlike vanilla data types and data family declarations, data family
-- instance declarations do not come equipped with a list of bound type
-- variables (at least not yet—see Trac #14268). This means that we have
-- to reverse engineer this information ourselves from the list of type
-- patterns. We accomplish this by taking the free variables of the types
-- and performing a reverse topological sort on them to ensure that the
-- returned list is well scoped.
dataFamInstTvbs :: [DType] -> [DTyVarBndr]
dataFamInstTvbs = toposortTyVarsOf

-- | Take a list of 'DType's, find their free variables, and sort them in
-- reverse topological order to ensure that they are well scoped.
--
-- On older GHCs, this takes measures to avoid returning explicitly bound
-- kind variables, which was not possible before @TypeInType@.
toposortTyVarsOf :: [DType] -> [DTyVarBndr]
toposortTyVarsOf tys =
  let fvs :: [Name]
      fvs = Set.toList $ foldMap fvDType tys

      varKindSigs :: Map Name DKind
      varKindSigs = foldMap go tys
        where
          go :: DType -> Map Name DKind
          go (DForallT {}) = error "`forall` type used in type family pattern"
          go (DAppT t1 t2) = go t1 `mappend` go t2
          go (DSigT t k) =
            let kSigs = go k
            in case t of
                 DVarT n -> Map.insert n k kSigs
                 _       -> go t `mappend` kSigs
          go (DVarT {}) = mempty
          go (DConT {}) = mempty
          go DArrowT    = mempty
          go (DLitT {}) = mempty
          go DWildCardT = mempty

      (g, gLookup, _)
        = graphFromEdges [ (fv, fv, kindVars)
                         | fv <- fvs
                         , let kindVars =
                                 case Map.lookup fv varKindSigs of
                                   Nothing -> []
                                   Just ks -> Set.toList (fvDType ks)
                         ]
      tg = reverse $ topSort g

      lookupVertex x =
        case gLookup x of
          (n, _, _) -> n

      ascribeWithKind n
        | Just k <- Map.lookup n varKindSigs
        = DKindedTV n k
        | otherwise
        = DPlainTV n

      -- An annoying wrinkle: GHCs before 8.0 don't support explicitly
      -- quantifying kinds, so something like @forall k (a :: k)@ would be
      -- rejected. To work around this, we filter out any binders whose names
      -- also appear in a kind on old GHCs.
      isKindBinderOnOldGHCs
#if __GLASGOW_HASKELL__ >= 800
        = const False
#else
        = (`elem` kindVars)
          where
            kindVars = foldMap fvDType $ Map.elems varKindSigs
#endif

  in map ascribeWithKind $
     filter (not . isKindBinderOnOldGHCs) $
     map lookupVertex tg

fvDType :: DType -> S.Set Name
fvDType = go_ty
  where
    go_ty :: DType -> S.Set Name
    go_ty (DForallT tvbs cxt ty) = (foldMap go_tvb tvbs <> go_ty ty <> foldMap go_pred cxt)
                                   S.\\ S.fromList (map dtvbName tvbs)
    go_ty (DAppT t1 t2)          = go_ty t1 <> go_ty t2
    go_ty (DSigT ty ki)          = go_ty ty <> go_ty ki
    go_ty (DVarT n)              = S.singleton n
    go_ty (DConT {})             = S.empty
    go_ty DArrowT                = S.empty
    go_ty (DLitT {})             = S.empty
    go_ty DWildCardT             = S.empty

    go_pred :: DPred -> S.Set Name
    go_pred (DAppPr pr ty) = go_pred pr <> go_ty ty
    go_pred (DSigPr pr ki) = go_pred pr <> go_ty ki
    go_pred (DVarPr n)     = S.singleton n
    go_pred _              = S.empty

    go_tvb :: DTyVarBndr -> S.Set Name
    go_tvb (DPlainTV{})    = S.empty
    go_tvb (DKindedTV _ k) = go_ty k

dtvbName :: DTyVarBndr -> Name
dtvbName (DPlainTV n)    = n
dtvbName (DKindedTV n _) = n

-- | Decompose a function type into its type variables, its context, its
-- argument types, and its result type.
unravel :: DType -> ([DTyVarBndr], [DPred], [DType], DType)
unravel (DForallT tvbs cxt ty) =
  let (tvbs', cxt', tys, res) = unravel ty in
  (tvbs ++ tvbs', cxt ++ cxt', tys, res)
unravel (DAppT (DAppT DArrowT t1) t2) =
  let (tvbs, cxt, tys, res) = unravel t2 in
  (tvbs, cxt, t1 : tys, res)
unravel t = ([], [], [], t)
