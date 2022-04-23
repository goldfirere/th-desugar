{- Language/Haskell/TH/Desugar/AST.hs

(c) Ryan Scott 2018

Defines the desugared Template Haskell AST. The desugared types and
constructors are prefixed with a D.
-}

{-# LANGUAGE CPP, DeriveDataTypeable, DeriveFunctor, DeriveGeneric #-}

module Language.Haskell.TH.Desugar.AST where

import Data.Data hiding (Fixity)
import GHC.Generics hiding (Fixity)
import Language.Haskell.TH
#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH.Datatype.TyVarBndr (Specificity)
#endif

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
          deriving (Eq, Show, Data, Generic)


-- | Corresponds to TH's @Pat@ type.
data DPat = DLitP Lit
          | DVarP Name
          | DConP Name [DType] [DPat]
          | DTildeP DPat
          | DBangP DPat
          | DSigP DPat DType
          | DWildP
          deriving (Eq, Show, Data, Generic)

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
           deriving (Eq, Show, Data, Generic)

-- | The type variable binders in a @forall@.
data DForallTelescope
  = DForallVis   [DTyVarBndrUnit]
    -- ^ A visible @forall@ (e.g., @forall a -> {...}@).
    --   These do not have any notion of specificity, so we use
    --   '()' as a placeholder value in the 'DTyVarBndr's.
  | DForallInvis [DTyVarBndrSpec]
    -- ^ An invisible @forall@ (e.g., @forall a {b} c -> {...}@),
    --   where each binder has a 'Specificity'.
  deriving (Eq, Show, Data, Generic)

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
  deriving (Eq, Show, Data, Generic, Functor)

-- | Corresponds to TH's @TyVarBndrSpec@
type DTyVarBndrSpec = DTyVarBndr Specificity

-- | Corresponds to TH's @TyVarBndrUnit@
type DTyVarBndrUnit = DTyVarBndr ()

-- | Corresponds to TH's @Match@ type.
data DMatch = DMatch DPat DExp
  deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @Clause@ type.
data DClause = DClause [DPat] DExp
  deriving (Eq, Show, Data, Generic)

-- | Declarations as used in a @let@ statement.
data DLetDec = DFunD Name [DClause]
             | DValD DPat DExp
             | DSigD Name DType
             | DInfixD Fixity Name
             | DPragmaD DPragma
             deriving (Eq, Show, Data, Generic)

-- | Is it a @newtype@ or a @data@ type?
data NewOrData = Newtype
               | Data
               deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @Dec@ type.
data DDec = DLetDec DLetDec
          | DDataD NewOrData DCxt Name [DTyVarBndrUnit] (Maybe DKind) [DCon] [DDerivClause]
          | DTySynD Name [DTyVarBndrUnit] DType
          | DClassD DCxt Name [DTyVarBndrUnit] [FunDep] [DDec]
            -- | Note that the @Maybe [DTyVarBndrUnit]@ field is dropped
            -- entirely when sweetened, so it is only useful for functions
            -- that directly consume @DDec@s.
          | DInstanceD (Maybe Overlap) (Maybe [DTyVarBndrUnit]) DCxt DType [DDec]
          | DForeignD DForeign
          | DOpenTypeFamilyD DTypeFamilyHead
          | DClosedTypeFamilyD DTypeFamilyHead [DTySynEqn]
          | DDataFamilyD Name [DTyVarBndrUnit] (Maybe DKind)
          | DDataInstD NewOrData DCxt (Maybe [DTyVarBndrUnit]) DType (Maybe DKind)
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
          deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's 'PatSynDir' type
data DPatSynDir = DUnidir              -- ^ @pattern P x {<-} p@
                | DImplBidir           -- ^ @pattern P x {=} p@
                | DExplBidir [DClause] -- ^ @pattern P x {<-} p where P x = e@
                deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's 'PatSynType' type
type DPatSynType = DType

#if __GLASGOW_HASKELL__ < 801
-- | Same as @PatSynArgs@ from TH; defined here for backwards compatibility.
data PatSynArgs
  = PrefixPatSyn [Name]        -- ^ @pattern P {x y z} = p@
  | InfixPatSyn Name Name      -- ^ @pattern {x P y} = p@
  | RecordPatSyn [Name]        -- ^ @pattern P { {x,y,z} } = p@
  deriving (Eq, Show, Data, Generic)
#endif

-- | Corresponds to TH's 'TypeFamilyHead' type
data DTypeFamilyHead = DTypeFamilyHead Name [DTyVarBndrUnit] DFamilyResultSig
                                       (Maybe InjectivityAnn)
                     deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's 'FamilyResultSig' type
data DFamilyResultSig = DNoSig
                      | DKindSig DKind
                      | DTyVarSig DTyVarBndrUnit
                      deriving (Eq, Show, Data, Generic)

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
          deriving (Eq, Show, Data, Generic)

-- | A list of fields either for a standard data constructor or a record
-- data constructor.
data DConFields = DNormalC DDeclaredInfix [DBangType]
                | DRecC [DVarBangType]
                deriving (Eq, Show, Data, Generic)

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
              deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @Pragma@ type.
data DPragma = DInlineP Name Inline RuleMatch Phases
             | DSpecialiseP Name DType (Maybe Inline) Phases
             | DSpecialiseInstP DType
             | DRuleP String (Maybe [DTyVarBndrUnit]) [DRuleBndr] DExp DExp Phases
             | DAnnP AnnTarget DExp
             | DLineP Int String
             | DCompleteP [Name] (Maybe Name)
             deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @RuleBndr@ type.
data DRuleBndr = DRuleVar Name
               | DTypedRuleVar Name DType
               deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @TySynEqn@ type (to store type family equations).
data DTySynEqn = DTySynEqn (Maybe [DTyVarBndrUnit]) DType DType
               deriving (Eq, Show, Data, Generic)

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
           deriving (Eq, Show, Data, Generic)

type DInstanceDec = DDec -- ^ Guaranteed to be an instance declaration

-- | Corresponds to TH's @DerivClause@ type.
data DDerivClause = DDerivClause (Maybe DDerivStrategy) DCxt
                  deriving (Eq, Show, Data, Generic)

-- | Corresponds to TH's @DerivStrategy@ type.
data DDerivStrategy = DStockStrategy     -- ^ A \"standard\" derived instance
                    | DAnyclassStrategy  -- ^ @-XDeriveAnyClass@
                    | DNewtypeStrategy   -- ^ @-XGeneralizedNewtypeDeriving@
                    | DViaStrategy DType -- ^ @-XDerivingVia@
                    deriving (Eq, Show, Data, Generic)
