{- Language/Haskell/TH/Desugar/AST.hs

(c) Ryan Scott 2018

Defines the desugared Template Haskell AST. The desugared types and
constructors are prefixed with a D.
-}

{-# LANGUAGE CPP, DeriveDataTypeable, DeriveTraversable, DeriveGeneric, DeriveLift, PatternSynonyms, ViewPatterns #-}

module Language.Haskell.TH.Desugar.AST where

import Data.Data hiding (Fixity)
import GHC.Generics hiding (Fixity)
import Language.Haskell.TH
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Lift)
#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH.Datatype.TyVarBndr (Specificity(..))
#endif
#if __GLASGOW_HASKELL__ < 907
import Language.Haskell.TH.Datatype.TyVarBndr (BndrVis)
#endif

import Language.Haskell.TH.Desugar.Util (DataFlavor)

-- | Corresponds to TH's @Exp@ type. Note that @DLamE@ takes names, not patterns.
data DExp = DVarE Name
          | DConE Name
          | DLitE Lit
          | DAppE DExp DExp
          | DAppTypeE DExp DType
            -- | A @\\cases@ expression. In the spirit of making 'DExp' minimal,
            -- @th-desugar@ will desugar lambda expressions, @case@ expressions,
            -- @\\case@ expressions, and @\\cases@ expressions to 'DLamCasesE'.
            -- (See also the 'dLamE', 'dCaseE', and 'dLamCaseE' functions for
            -- constructing these expressions in terms of 'DLamCasesE'.)
            --
            -- A 'DLamCasesE' value should obey the following invariants:
            --
            -- * Each 'DClause' should have exactly the same number of visible
            --   arguments in its list of 'DPat's.
            --
            -- * If the list of 'DClause's is empty, then the overall expression
            --   should have exactly one argument. Note that this is a
            --   difference in behavior from how @\\cases@ expressions work, as
            --   @\\cases@ is required to have at least one clause. For this
            --   reason, @th-desugar@ will sweeten @DLamCasesE []@ to
            --   @\\case{}@.
          | DLamCasesE [DClause]
          | DLetE [DLetDec] DExp
          | DSigE DExp DType
          | DStaticE DExp
          | DTypedBracketE DExp
          | DTypedSpliceE DExp
          | DTypeE DType
          | DForallE DForallTelescope DExp
          | DConstrainedE [DExp] DExp
          deriving (Eq, Show, Data, Generic, Lift)

-- | A 'DLamCasesE' value with exactly one 'DClause' where all 'DPat's are
-- 'DVarP's. This pattern synonym is provided for backwards compatibility with
-- older versions of @th-desugar@ in which 'DLamE' was a data constructor of
-- 'DExp'. This pattern synonym is deprecated and will be removed in a future
-- release of @th-desugar@.
pattern DLamE :: [Name] -> DExp -> DExp
pattern DLamE vars rhs <- (dLamE_maybe -> Just (vars, rhs))
  where
    DLamE vars rhs = DLamCasesE [DClause (map DVarP vars) rhs]
{-# DEPRECATED DLamE "Use `dLamE` or `DLamCasesE` instead." #-}

-- | Return @'Just' (pats, rhs)@ if the supplied 'DExp' is a 'DLamCasesE' value
-- with exactly one 'DClause' where all 'DPat's are 'DVarP's, where @pats@ is
-- the list of 'DVarP' 'Name's and @rhs@ is the expression on the right-hand
-- side of the 'DClause'. Otherwise, return 'Nothing'.
dLamE_maybe :: DExp -> Maybe ([Name], DExp)
dLamE_maybe (DLamCasesE [DClause pats rhs]) = do
  vars <- traverse dVarP_maybe pats
  Just (vars, rhs)
dLamE_maybe _ = Nothing

-- | Return @'Just' var@ if the supplied 'DPat' is a 'DVarP' value, where @var@
-- is the 'DVarP' 'Name'. Otherwise, return 'Nothing'.
dVarP_maybe :: DPat -> Maybe Name
dVarP_maybe (DVarP n) = Just n
dVarP_maybe _         = Nothing

-- | An application of a 'DLamCasesE' to some argument, where each 'DClause' in
-- the 'DLamCasesE' value has exactly one 'DPat'. This pattern synonym is
-- provided for backwards compatibility with older versions of @th-desugar@ in
-- which 'DCaseE' was a data constructor of 'DExp'. This pattern synonym is
-- deprecated and will be removed in a future release of @th-desugar@.
pattern DCaseE :: DExp -> [DMatch] -> DExp
pattern DCaseE scrut matches <- (dCaseE_maybe -> Just (scrut, matches))
  where
    DCaseE scrut matches = DAppE (dLamCaseE matches) scrut
{-# DEPRECATED DCaseE "Use `dCaseE` or `DLamCasesE` instead." #-}

-- | Return @'Just' (scrut, matches)@ if the supplied 'DExp' is a 'DLamCasesE'
-- value applied to some argument, where each 'DClause' in the 'DLamCasesE'
-- value has exactly one 'DPat'. Otherwise, return 'Nothing'.
dCaseE_maybe :: DExp -> Maybe (DExp, [DMatch])
dCaseE_maybe (DAppE (DLamCasesE clauses) scrut) = do
  matches <- traverse dMatch_maybe clauses
  Just (scrut, matches)
dCaseE_maybe _  = Nothing

-- | Construct a 'DExp' value that is equivalent to writing a @case@ expression.
-- Under the hood, this uses @\\cases@ ('DLamCasesE'). For instance, given this
-- code:
--
-- @
-- case scrut of
--   pat_1 -> rhs_1
--   ...
--   pat_n -> rhs_n
-- @
--
-- The following @\\cases@ expression will be created under the hood:
--
-- @
-- (\\cases
--   pat_1 -> rhs_1
--   ...
--   pat_n -> rhs_n) scrut
-- @
dCaseE :: DExp -> [DMatch] -> DExp
dCaseE scrut matches = DAppE (dLamCaseE matches) scrut

-- | Construct a 'DExp' value that is equivalent to writing a lambda expression.
-- Under the hood, this uses @\\cases@ ('DLamCasesE'). For instance, given this
-- code:
--
-- @
-- \\var_1 ... var_n -> rhs
-- @
--
-- The following @\\cases@ expression will be created under the hood:
--
-- @
-- \\cases var_1 ... var_n -> rhs
-- @
dLamE :: [DPat] -> DExp -> DExp
dLamE pats rhs = DLamCasesE [DClause pats rhs]

-- | Construct a 'DExp' value that is equivalent to writing a @\\case@
-- expression. Under the hood, this uses @\\cases@ ('DLamCasesE'). For instance,
-- given this code:
--
-- @
-- \\case
--   pat_1 -> rhs_1
--   ...
--   pat_n -> rhs_n
-- @
--
-- The following @\\cases@ expression will be created under the hood:
--
-- @
-- \\cases
--   pat_1 -> rhs_1
--   ...
--   pat_n -> rhs_n
-- @
dLamCaseE :: [DMatch] -> DExp
dLamCaseE = DLamCasesE . map dMatchToDClause

-- | Corresponds to TH's @Pat@ type.
data DPat = DLitP Lit
          | DVarP Name
          | DConP Name [DType] [DPat]
          | DTildeP DPat
          | DBangP DPat
          | DSigP DPat DType
          | DWildP
          | DTypeP DType
          | DInvisP DType
          deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's @Type@ type, used to represent
-- types and kinds.
data DType = DForallT DForallTelescope DType
           | DConstrainedT DCxt DType
           | DAppT DType DType
           | DAppKindT DType DKind
           | DSigT DType DKind
           | DVarT Name
           | DConT Name
           | DArrowT
           | DLitT TyLit
           | DWildCardT
           deriving (Eq, Show, Data, Generic, Lift)

-- | The type variable binders in a @forall@.
data DForallTelescope
  = DForallVis   [DTyVarBndrUnit]
    -- ^ A visible @forall@ (e.g., @forall a -> {...}@).
    --   These do not have any notion of specificity, so we use
    --   '()' as a placeholder value in the 'DTyVarBndr's.
  | DForallInvis [DTyVarBndrSpec]
    -- ^ An invisible @forall@ (e.g., @forall a {b} c -> {...}@),
    --   where each binder has a 'Specificity'.
  deriving (Eq, Show, Data, Generic, Lift)

-- | Kinds are types. Corresponds to TH's @Kind@
type DKind = DType

-- | Predicates are types. Corresponds to TH's @Pred@
type DPred = DType

-- | Corresponds to TH's @Cxt@
type DCxt = [DPred]

-- | Corresponds to TH's @TyVarBndr@
data DTyVarBndr flag
  = DPlainTV Name flag
  | DKindedTV Name flag DKind
  deriving (Eq, Show, Data, Generic, Functor, Foldable, Traversable, Lift)

-- | Corresponds to TH's @TyVarBndrSpec@
type DTyVarBndrSpec = DTyVarBndr Specificity

-- | Corresponds to TH's @TyVarBndrUnit@
type DTyVarBndrUnit = DTyVarBndr ()

-- | Corresponds to TH's @TyVarBndrVis@
type DTyVarBndrVis = DTyVarBndr BndrVis

-- | Corresponds to TH's @Match@ type.
--
-- Note that while @Match@ appears in the TH AST, 'DMatch' does not appear
-- directly in the @th-desugar@ AST. This is because TH's 'Match' is used in
-- lambda (@LamE@) and @case@ (@CaseE@) expressions, but @th-desugar@ does not
-- have counterparts to @LamE@ and @CaseE@ in the 'DExp' data type. Instead,
-- 'DExp' only has a @\\cases@ ('DLamCasesE') construct, which uses 'DClause'
-- instead of 'DMatch'.
--
-- As such, 'DMatch' only plays a \"vestigial\" role in @th-desugar@ for
-- constructing 'DLamCasesE' values that look like lambda or @case@ expressions.
-- For example, 'DMatch' appears in the type signatures for 'dLamE' and
-- 'dCaseE', which convert the supplied 'DMatch'es to 'DClause's under the hood.
data DMatch = DMatch DPat DExp
  deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's @Clause@ type.
data DClause = DClause [DPat] DExp
  deriving (Eq, Show, Data, Generic, Lift)

-- | Convert a 'DMatch' to a 'DClause', where the 'DClause' contains a single
-- pattern taken from the 'DMatch'.
dMatchToDClause :: DMatch -> DClause
dMatchToDClause (DMatch pat rhs) = DClause [pat] rhs

-- | Return @'Just' match@ if the supplied 'DClause' has exactly one 'DPat',
-- where @match@ matches on that 'DPat'. Otherwise, return 'Nothing'.
dMatch_maybe :: DClause -> Maybe DMatch
dMatch_maybe (DClause pats rhs) =
  case pats of
    [pat] -> Just (DMatch pat rhs)
    _     -> Nothing

-- | Declarations as used in a @let@ statement.
data DLetDec = DFunD Name [DClause]
             | DValD DPat DExp
             | DSigD Name DType
             | DInfixD Fixity NamespaceSpecifier Name
             | DPragmaD DPragma
             deriving (Eq, Show, Data, Generic, Lift)

#if __GLASGOW_HASKELL__ < 909
-- | Same as @NamespaceSpecifier@ from TH; defined here for backwards
-- compatibility.
data NamespaceSpecifier
  = NoNamespaceSpecifier   -- ^ Name may be everything; If there are two
                           --   names in different namespaces, then consider both
  | TypeNamespaceSpecifier -- ^ Name should be a type-level entity, such as a
                           --   data type, type alias, type family, type class,
                           --   or type variable
  | DataNamespaceSpecifier -- ^ Name should be a term-level entity, such as a
                           --   function, data constructor, or pattern synonym
  deriving (Eq, Ord, Show, Data, Generic, Lift)
#endif

-- | Corresponds to TH's @Dec@ type.
data DDec = DLetDec DLetDec
            -- | An ordinary (i.e., non-data family) data type declaration. Note
            -- that desugaring upholds the following properties regarding the
            -- 'DataFlavor' field:
            --
            -- * If the 'DataFlavor' is 'NewType', then there will be exactly
            --   one 'DCon'.
            --
            -- * If the 'DataFlavor' is 'TypeData', then there will be no
            --   'DDerivClause's, the 'DCxt' will be empty, and the 'DConFields'
            --   in each 'DCon' will be a 'NormalC' where each 'Bang' is equal
            --   to @Bang 'NoSourceUnpackedness' 'NoSourceStrictness'@.
          | DDataD DataFlavor DCxt Name [DTyVarBndrVis] (Maybe DKind) [DCon] [DDerivClause]
          | DTySynD Name [DTyVarBndrVis] DType
          | DClassD DCxt Name [DTyVarBndrVis] [FunDep] [DDec]
            -- | Note that the @Maybe [DTyVarBndrUnit]@ field is dropped
            -- entirely when sweetened, so it is only useful for functions
            -- that directly consume @DDec@s.
          | DInstanceD (Maybe Overlap) (Maybe [DTyVarBndrUnit]) DCxt DType [DDec]
          | DForeignD DForeign
          | DOpenTypeFamilyD DTypeFamilyHead
          | DClosedTypeFamilyD DTypeFamilyHead [DTySynEqn]
          | DDataFamilyD Name [DTyVarBndrVis] (Maybe DKind)
            -- | A data family instance declaration. Note that desugaring
            -- upholds the following properties regarding the 'DataFlavor'
            -- field:
            --
            -- * If the 'DataFlavor' is 'NewType', then there will be exactly
            --   one 'DCon'.
            --
            -- * The 'DataFlavor' will never be 'TypeData', as GHC does not
            --   permit combining data families with @type data@.
          | DDataInstD DataFlavor DCxt (Maybe [DTyVarBndrUnit]) DType (Maybe DKind)
                       [DCon] [DDerivClause]
          | DTySynInstD DTySynEqn
          | DRoleAnnotD Name [Role]
            -- | Note that the @Maybe [DTyVarBndrUnit]@ field is dropped
            -- entirely when sweetened, so it is only useful for functions
            -- that directly consume @DDec@s.
          | DStandaloneDerivD (Maybe DDerivStrategy) (Maybe [DTyVarBndrUnit]) DCxt DType
          | DDefaultSigD Name DType
          | DPatSynD Name PatSynArgs DPatSynDir DPat
          | DPatSynSigD Name DPatSynType
          | DKiSigD Name DKind
              -- DKiSigD is part of DDec, not DLetDec, because standalone kind
              -- signatures can only appear on the top level.
          | DDefaultD [DType]
          deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's 'PatSynDir' type
data DPatSynDir = DUnidir              -- ^ @pattern P x {<-} p@
                | DImplBidir           -- ^ @pattern P x {=} p@
                | DExplBidir [DClause] -- ^ @pattern P x {<-} p where P x = e@
                deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's 'PatSynType' type
type DPatSynType = DType

#if __GLASGOW_HASKELL__ < 801
-- | Same as @PatSynArgs@ from TH; defined here for backwards compatibility.
data PatSynArgs
  = PrefixPatSyn [Name]        -- ^ @pattern P {x y z} = p@
  | InfixPatSyn Name Name      -- ^ @pattern {x P y} = p@
  | RecordPatSyn [Name]        -- ^ @pattern P { {x,y,z} } = p@
  deriving (Eq, Show, Data, Generic, Lift)
#endif

-- | Corresponds to TH's 'TypeFamilyHead' type
data DTypeFamilyHead = DTypeFamilyHead Name [DTyVarBndrVis] DFamilyResultSig
                                       (Maybe InjectivityAnn)
                     deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's 'FamilyResultSig' type
data DFamilyResultSig = DNoSig
                      | DKindSig DKind
                      | DTyVarSig DTyVarBndrUnit
                      deriving (Eq, Show, Data, Generic, Lift)

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
data DCon = DCon [DTyVarBndrSpec] DCxt Name DConFields
                 DType  -- ^ The GADT result type
          deriving (Eq, Show, Data, Generic, Lift)

-- | A list of fields either for a standard data constructor or a record
-- data constructor.
data DConFields = DNormalC DDeclaredInfix [DBangType]
                | DRecC [DVarBangType]
                deriving (Eq, Show, Data, Generic, Lift)

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

-- | Corresponds to TH's @Foreign@ type.
data DForeign = DImportF Callconv Safety String Name DType
              | DExportF Callconv String Name DType
              deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's @Pragma@ type.
data DPragma = DInlineP Name Inline RuleMatch Phases
             | DSpecialiseEP (Maybe [DTyVarBndr ()]) [DRuleBndr] DExp (Maybe Inline) Phases
             | DSpecialiseInstP DType
             | DRuleP String (Maybe [DTyVarBndrUnit]) [DRuleBndr] DExp DExp Phases
             | DAnnP AnnTarget DExp
             | DLineP Int String
             | DCompleteP [Name] (Maybe Name)
             | DOpaqueP Name
             | DSCCP Name (Maybe String)
             deriving (Eq, Show, Data, Generic, Lift)

-- | Old-form specialise pragma @{ {\-\# SPECIALISE [INLINE] [phases] (var :: ty) #-} }@.
--
-- Subsumed by the more general 'DSpecialiseEP' constructor.
pattern DSpecialiseP :: Name -> DType -> Maybe Inline -> Phases -> DPragma
pattern DSpecialiseP nm ty inl phases = DSpecialiseEP Nothing [] (DSigE (DVarE nm) ty) inl phases

-- | Corresponds to TH's @RuleBndr@ type.
data DRuleBndr = DRuleVar Name
               | DTypedRuleVar Name DType
               deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's @TySynEqn@ type (to store type family equations).
data DTySynEqn = DTySynEqn (Maybe [DTyVarBndrUnit]) DType DType
               deriving (Eq, Show, Data, Generic, Lift)

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
           deriving (Eq, Show, Data, Generic, Lift)

type DInstanceDec = DDec -- ^ Guaranteed to be an instance declaration

-- | Corresponds to TH's @DerivClause@ type.
data DDerivClause = DDerivClause (Maybe DDerivStrategy) DCxt
                  deriving (Eq, Show, Data, Generic, Lift)

-- | Corresponds to TH's @DerivStrategy@ type.
data DDerivStrategy = DStockStrategy     -- ^ A \"standard\" derived instance
                    | DAnyclassStrategy  -- ^ @-XDeriveAnyClass@
                    | DNewtypeStrategy   -- ^ @-XGeneralizedNewtypeDeriving@
                    | DViaStrategy DType -- ^ @-XDerivingVia@
                    deriving (Eq, Show, Data, Generic, Lift)
