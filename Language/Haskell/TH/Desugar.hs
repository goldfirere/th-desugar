{- Language/Haskell/TH/Desugar.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Desugars full Template Haskell syntax into a smaller core syntax for further
-- processing. The desugared types and constructors are prefixed with a D.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar (
  -- * Desugared data types
  DExp(..), DLetDec(..), DPat(..), DType(..), DKind, DCxt, DPred(..),
  DTyVarBndr(..), DMatch(..), DClause(..), DDec(..),
  DDerivClause(..), DerivStrategy(..), DPatSynDir(..), DPatSynType,
  Overlap(..), PatSynArgs(..), NewOrData(..),
  DTypeFamilyHead(..), DFamilyResultSig(..), InjectivityAnn(..),
  DCon(..), DConFields(..), DDeclaredInfix, DBangType, DVarBangType,
  Bang(..), SourceUnpackedness(..), SourceStrictness(..),
  DForeign(..),
  DPragma(..), DRuleBndr(..), DTySynEqn(..), DInfo(..), DInstanceDec,
  Role(..), AnnTarget(..),

  -- * The 'Desugar' class
  Desugar(..),

  -- * Main desugaring functions
  dsExp, dsDecs, dsType, dsInfo,
  dsPatOverExp, dsPatsOverExp, dsPatX,
  dsLetDecs, dsTvb, dsCxt,
  dsCon, dsForeign, dsPragma, dsRuleBndr,

  -- ** Secondary desugaring functions
  PatM, dsPred, dsPat, dsDec, dsDerivClause, dsLetDec,
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses,
  dsBangType, dsVarBangType,
#if __GLASGOW_HASKELL__ > 710
  dsTypeFamilyHead, dsFamilyResultSig,
#endif
#if __GLASGOW_HASKELL__ >= 801
  dsPatSynDir,
#endif

  -- * Converting desugared AST back to TH AST
  module Language.Haskell.TH.Desugar.Sweeten,

  -- * Expanding type synonyms
  expand, expandType,

  -- * Reification
  reifyWithWarning,

  -- | The following definitions allow you to register a list of
  -- @Dec@s to be used in reification queries.
  withLocalDeclarations, dsReify,
  reifyWithLocals_maybe, reifyWithLocals, reifyFixityWithLocals,
  lookupValueNameWithLocals, lookupTypeNameWithLocals,
  mkDataNameWithLocals, mkTypeNameWithLocals,
  reifyNameSpace,
  DsMonad(..), DsM,

  -- * Nested pattern flattening
  scExp, scLetDec,

  -- * Capture-avoiding substitution and utilities
  module Language.Haskell.TH.Desugar.Subst,

  -- * Utility functions
  applyDExp, applyDType,
  dPatToDExp, removeWilds,
  getDataD, dataConNameToDataName, dataConNameToCon,
  nameOccursIn, allNamesIn, flattenDValD, getRecordSelectors,
  mkTypeName, mkDataName, newUniqueName,
  mkTupleDExp, mkTupleDPat, maybeDLetE, maybeDCaseE, mkDLamEFromDPats,
  fvDType,
  tupleDegree_maybe, tupleNameDegree_maybe,
  unboxedSumDegree_maybe, unboxedSumNameDegree_maybe,
  unboxedTupleDegree_maybe, unboxedTupleNameDegree_maybe,
  strictToBang, isTypeKindName, typeKindName,
  unravel, conExistentialTvbs, mkExtraDKindBinders,
  dTyVarBndrToDType, toposortTyVarsOf,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Desugar.Reify
import Language.Haskell.TH.Desugar.Expand
import Language.Haskell.TH.Desugar.Match
import Language.Haskell.TH.Desugar.Subst

import Control.Monad
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding ( exp )

-- | This class relates a TH type with its th-desugar type and allows
-- conversions back and forth. The functional dependency goes only one
-- way because `Type` and `Kind` are type synonyms, but they desugar
-- to different types.
class Desugar th ds | ds -> th where
  desugar :: DsMonad q => th -> q ds
  sweeten :: ds -> th

instance Desugar Exp DExp where
  desugar = dsExp
  sweeten = expToTH

instance Desugar Type DType where
  desugar = dsType
  sweeten = typeToTH

instance Desugar Cxt DCxt where
  desugar = dsCxt
  sweeten = cxtToTH

instance Desugar TyVarBndr DTyVarBndr where
  desugar = dsTvb
  sweeten = tvbToTH

instance Desugar [Dec] [DDec] where
  desugar = dsDecs
  sweeten = decsToTH

-- | If the declaration passed in is a 'DValD', creates new, equivalent
-- declarations such that the 'DPat' in all 'DValD's is just a plain
-- 'DVarPa'. Other declarations are passed through unchanged.
-- Note that the declarations that come out of this function are rather
-- less efficient than those that come in: they have many more pattern
-- matches.
flattenDValD :: Quasi q => DLetDec -> q [DLetDec]
flattenDValD dec@(DValD (DVarPa _) _) = return [dec]
flattenDValD (DValD pat exp) = do
  x <- newUniqueName "x" -- must use newUniqueName here because we might be top-level
  let top_val_d = DValD (DVarPa x) exp
      bound_names = S.elems $ extractBoundNamesDPat pat
  other_val_ds <- mapM (mk_val_d x) bound_names
  return $ top_val_d : other_val_ds
  where
    mk_val_d x name = do
      y <- newUniqueName "y"
      let pat'  = wildify name y pat
          match = DMatch pat' (DVarE y)
          cas   = DCaseE (DVarE x) [match]
      return $ DValD (DVarPa name) cas

    wildify name y p =
      case p of
        DLitPa lit -> DLitPa lit
        DVarPa n
          | n == name -> DVarPa y
          | otherwise -> DWildPa
        DConPa con ps -> DConPa con (map (wildify name y) ps)
        DTildePa pa -> DTildePa (wildify name y pa)
        DBangPa pa -> DBangPa (wildify name y pa)
        DSigPa pa ty -> DSigPa (wildify name y pa) ty
        DWildPa -> DWildPa

flattenDValD other_dec = return [other_dec]

-- | Produces 'DLetDec's representing the record selector functions from
-- the provided 'DCon's.
--
-- Note that if the same record selector appears in multiple constructors,
-- 'getRecordSelectors' will return only one binding for that selector.
-- For example, if you had:
--
-- @
-- data X = X1 {y :: Symbol} | X2 {y :: Symbol}
-- @
--
-- Then calling 'getRecordSelectors' on @[X1, X2]@ will return:
--
-- @
-- [ DSigD y (DAppT (DAppT DArrowT (DConT X)) (DConT Symbol))
-- , DFunD y [ DClause [DConPa X1 [DVarPa field]] (DVarE field)
--           , DClause [DConPa X2 [DVarPa field]] (DVarE field) ] ]
-- @
--
-- instead of returning one binding for @X1@ and another binding for @X2@.
--
-- 'getRecordSelectors' attempts to filter out \"naughty\" record selectors
-- whose types mention existentially quantified type variables. But see the
-- documentation for 'conExistentialTvbs' for limitations to this approach.

-- See https://github.com/goldfirere/singletons/issues/180 for an example where
-- the latter behavior can bite you.

getRecordSelectors :: Quasi q
                   => DType        -- ^ the type of the argument
                   -> [DCon]
                   -> q [DLetDec]
getRecordSelectors arg_ty cons = merge_let_decs `fmap` concatMapM get_record_sels cons
  where
    get_record_sels (DCon _ _ con_name con _) = case con of
      DRecC fields -> go fields
      _ -> return []
      where
        go fields = do
          varName <- qNewName "field"
          let tvbs     = fvDType arg_ty
              forall'  = DForallT (map DPlainTV $ S.toList tvbs) []
              num_pats = length fields
          return $ concat
            [ [ DSigD name (forall' $ DArrowT `DAppT` arg_ty `DAppT` res_ty)
              , DFunD name [DClause [DConPa con_name (mk_field_pats n num_pats varName)]
                                    (DVarE varName)] ]
            | ((name, _strict, res_ty), n) <- zip fields [0..]
            , fvDType res_ty `S.isSubsetOf` tvbs   -- exclude "naughty" selectors
            ]

    mk_field_pats :: Int -> Int -> Name -> [DPat]
    mk_field_pats 0 total name = DVarPa name : (replicate (total-1) DWildPa)
    mk_field_pats n total name = DWildPa : mk_field_pats (n-1) (total-1) name

    merge_let_decs :: [DLetDec] -> [DLetDec]
    merge_let_decs decs =
      let (name_clause_map, decs') = gather_decs M.empty S.empty decs
       in augment_clauses name_clause_map decs'
        -- First, for each record selector-related declarations, do the following:
        --
        -- 1. If it's a DFunD...
        --   a. If we haven't encountered it before, add a mapping from its Name
        --      to its associated DClauses, and continue.
        --   b. If we have encountered it before, augment the existing Name's
        --      mapping with the new clauses. Then remove the DFunD from the list
        --      and continue.
        -- 2. If it's a DSigD...
        --   a. If we haven't encountered it before, remember its Name and continue.
        --   b. If we have encountered it before, remove the DSigD from the list
        --      and continue.
        -- 3. Otherwise, continue.
        --
        -- After this, scan over the resulting list once more with the mapping
        -- that we accumulated. For every DFunD, replace its DClauses with the
        -- ones corresponding to its Name in the mapping.
        --
        -- Note that this algorithm combines all of the DClauses for each unique
        -- Name, while preserving the order in which the DFunDs were originally
        -- found. Moreover, it removes duplicate DSigD entries. Using Maps and
        -- Sets avoid quadratic blowup for data types with many record selectors.
      where
        gather_decs :: M.Map Name [DClause] -> S.Set Name -> [DLetDec]
                    -> (M.Map Name [DClause], [DLetDec])
        gather_decs name_clause_map _ [] = (name_clause_map, [])
        gather_decs name_clause_map type_sig_names (x:xs)
          -- 1.
          | DFunD n clauses <- x
          = let name_clause_map' = M.insertWith (\new old -> old ++ new)
                                                n clauses name_clause_map
             in if n `M.member` name_clause_map
                then gather_decs name_clause_map' type_sig_names xs
                else let (map', decs') = gather_decs name_clause_map'
                                           type_sig_names xs
                      in (map', x:decs')

          -- 2.
          | DSigD n _ <- x
          = if n `S.member` type_sig_names
            then gather_decs name_clause_map type_sig_names xs
            else let (map', decs') = gather_decs name_clause_map
                                       (n `S.insert` type_sig_names) xs
                  in (map', x:decs')

          -- 3.
          | otherwise =
              let (map', decs') = gather_decs name_clause_map type_sig_names xs
               in (map', x:decs')

        augment_clauses :: M.Map Name [DClause] -> [DLetDec] -> [DLetDec]
        augment_clauses _ [] = []
        augment_clauses name_clause_map (x:xs)
          | DFunD n _ <- x, Just merged_clauses <- n `M.lookup` name_clause_map
          = DFunD n merged_clauses:augment_clauses name_clause_map xs
          | otherwise = x:augment_clauses name_clause_map xs

-- | Create new kind variable binder names corresponding to the return kind of
-- a data type. This is useful when you have a data type like:
--
-- @
-- data Foo :: forall k. k -> Type -> Type where ...
-- @
--
-- But you want to be able to refer to the type @Foo a b@.
-- 'mkExtraDKindBinders' will take the kind @forall k. k -> Type -> Type@,
-- discover that is has two visible argument kinds, and return as a result
-- two new kind variable binders @[a :: k, b :: Type]@, where @a@ and @b@
-- are fresh type variable names.
--
-- This expands kind synonyms if necessary.
mkExtraDKindBinders :: DsMonad q => DKind -> q [DTyVarBndr]
mkExtraDKindBinders = expandType >=> mkExtraDKindBinders'

-- | Returns all of a constructor's existentially quantified type variable
-- binders.
--
-- Detecting the presence of existentially quantified type variables in the
-- context of Template Haskell is quite involved. Here is an example that
-- we will use to explain how this works:
--
-- @
-- data family Foo a b
-- data instance Foo (Maybe a) b where
--   MkFoo :: forall x y z. x -> y -> z -> Foo (Maybe x) [z]
-- @
--
-- In @MkFoo@, @x@ is universally quantified, whereas @y@ and @z@ are
-- existentially quantified. Note that @MkFoo@ desugars (in Core) to
-- something like this:
--
-- @
-- data instance Foo (Maybe a) b where
--   MkFoo :: forall a b y z. (b ~ [z]). a -> y -> z -> Foo (Maybe a) b
-- @
--
-- Here, we can see that @a@ appears in the desugared return type (it is a
-- simple alpha-renaming of @x@), so it is universally quantified. On the other
-- hand, neither @y@ nor @z@ appear in the desugared return type, so they are
-- existentially quantified.
--
-- This analysis would not have been possible without knowing what the original
-- data declaration's type was (in this case, @Foo (Maybe a) b@), which is why
-- we require it as an argument. Our algorithm for detecting existentially
-- quantified variables is not too different from what was described above:
-- we match the constructor's return type with the original data type, forming
-- a substitution, and check which quantified variables are not part of the
-- domain of the substitution.
--
-- Be warned: this may overestimate which variables are existentially
-- quantified when kind variables are involved. For instance, consider this
-- example:
--
-- @
-- data S k (a :: k)
-- data T a where
--   MkT :: forall k (a :: k). { foo :: Proxy (a :: k), bar :: S k a } -> T a
-- @
--
-- Here, the kind variable @k@ does not appear syntactically in the return type
-- @T a@, so 'conExistentialTvbs' would mistakenly flag @k@ as existential.
--
-- There are various tricks we could employ to improve this, but ultimately,
-- making this behave correctly with respect to @PolyKinds@ 100% of the time
-- would amount to performing kind inference in Template Haskell, which is
-- quite difficult. For the sake of simplicity, we have decided to stick with
-- a dumb-but-predictable syntactic check.
conExistentialTvbs :: DsMonad q
                   => DType -- ^ The type of the original data declaration
                   -> DCon
                   -> q [DTyVarBndr]
conExistentialTvbs data_ty (DCon tvbs _ _ _ ret_ty) =
  -- Due to GHC Trac #13885, it's possible that the type variables bound by
  -- a GADT constructor will shadow those that are bound by the data type.
  -- This function assumes this isn't the case in certain parts (e.g., when
  -- unifying types), so we do an alpha-renaming of the
  -- constructor-bound variables before proceeding.
  substTyVarBndrs M.empty tvbs $ \subst tvbs' -> do
    renamed_ret_ty <- substTy subst ret_ty
    data_ty'       <- expandType data_ty
    ret_ty'        <- expandType renamed_ret_ty
    case matchTy YesIgnore ret_ty' data_ty' of
      Nothing -> fail $ showString "Unable to match type "
                      . showsPrec 11 ret_ty'
                      . showString " with "
                      . showsPrec 11 data_ty'
                      $ ""
      Just gadtSubt -> return [ tvb
                              | tvb <- tvbs'
                              , M.notMember (dtvbName tvb) gadtSubt
                              ]
