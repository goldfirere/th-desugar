{- Language/Haskell/TH/Desugar.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE CPP, MultiParamTypeClasses, FunctionalDependencies,
             TypeSynonymInstances, FlexibleInstances, LambdaCase,
             ScopedTypeVariables #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Desugars full Template Haskell syntax into a smaller core syntax for further
-- processing.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar (
  -- * Desugared data types
  DExp(..), DLetDec(..), DPat(..),
  DType(..), DForallTelescope(..), DKind, DCxt, DPred,
  DTyVarBndr(..), DTyVarBndrSpec, DTyVarBndrUnit, Specificity(..),
  DMatch(..), DClause(..), DDec(..),
  DDerivClause(..), DDerivStrategy(..), DPatSynDir(..), DPatSynType,
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
  dsLetDecs, dsTvb, dsTvbSpec, dsTvbUnit, dsCxt,
  dsCon, dsForeign, dsPragma, dsRuleBndr,

  -- ** Secondary desugaring functions
  PatM, dsPred, dsPat, dsDec, dsDataDec, dsDataInstDec,
  DerivingClause, dsDerivClause, dsLetDec,
  dsMatches, dsBody, dsGuards, dsDoStmts, dsComp, dsClauses,
  dsBangType, dsVarBangType,
  dsTypeFamilyHead, dsFamilyResultSig,
#if __GLASGOW_HASKELL__ >= 801
  dsPatSynDir,
#endif
  dsTypeArg,

  -- * Converting desugared AST back to TH AST
  module Language.Haskell.TH.Desugar.Sweeten,

  -- * Expanding type synonyms
  expand, expandType,

  -- * Reification
  reifyWithWarning,

  -- ** Local reification
  -- $localReification
  withLocalDeclarations, dsReify, dsReifyType,
  reifyWithLocals_maybe, reifyWithLocals, reifyFixityWithLocals,
  reifyTypeWithLocals_maybe, reifyTypeWithLocals,
  lookupValueNameWithLocals, lookupTypeNameWithLocals,
  mkDataNameWithLocals, mkTypeNameWithLocals,
  reifyNameSpace,
  DsMonad(..), DsM,

  -- * Nested pattern flattening
  scExp, scLetDec,

  -- * Capture-avoiding substitution and utilities
  module Language.Haskell.TH.Desugar.Subst,

  -- * Free variable calculation
  module Language.Haskell.TH.Desugar.FV,

  -- * Utility functions
  applyDExp,
  dPatToDExp, removeWilds,
  getDataD, dataConNameToDataName, dataConNameToCon,
  nameOccursIn, allNamesIn, flattenDValD, getRecordSelectors,
  mkTypeName, mkDataName, newUniqueName,
  mkTupleDExp, mkTupleDPat, maybeDLetE, maybeDCaseE, mkDLamEFromDPats,
  tupleDegree_maybe, tupleNameDegree_maybe,
  unboxedSumDegree_maybe, unboxedSumNameDegree_maybe,
  unboxedTupleDegree_maybe, unboxedTupleNameDegree_maybe,
  isTypeKindName, typeKindName, bindIP,
  mkExtraDKindBinders, dTyVarBndrToDType, changeDTVFlags, toposortTyVarsOf,

  -- ** 'FunArgs' and 'VisFunArg'
  FunArgs(..), ForallTelescope(..), VisFunArg(..),
  filterVisFunArgs, ravelType, unravelType,

  -- ** 'DFunArgs' and 'DVisFunArg'
  DFunArgs(..), DVisFunArg(..),
  filterDVisFunArgs, ravelDType, unravelDType,

  -- ** 'TypeArg'
  TypeArg(..), applyType, filterTANormals, unfoldType,

  -- ** 'DTypeArg'
  DTypeArg(..), applyDType, filterDTANormals, unfoldDType,

  -- ** Extracting bound names
  extractBoundNamesStmt, extractBoundNamesDec, extractBoundNamesPat
  ) where

import Language.Haskell.TH.Datatype.TyVarBndr
import Language.Haskell.TH.Desugar.AST
import Language.Haskell.TH.Desugar.Core
import Language.Haskell.TH.Desugar.Expand
import Language.Haskell.TH.Desugar.FV
import Language.Haskell.TH.Desugar.Match
import Language.Haskell.TH.Desugar.Reify
import Language.Haskell.TH.Desugar.Subst
import Language.Haskell.TH.Desugar.Sweeten
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Syntax

import Control.Monad
import qualified Data.Foldable as F
import Data.Function
import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding ( exp )

-- | This class relates a TH type with its th-desugar type and allows
-- conversions back and forth. The functional dependency goes only one
-- way because we define the following instances on old versions of GHC:
--
-- @
-- instance 'Desugar' 'TyVarBndrSpec' 'DTyVarBndrSpec'
-- instance 'Desugar' 'TyVarBndrUnit' 'DTyVarBndrUnit'
-- @
--
-- Prior to GHC 9.0, 'TyVarBndrSpec' and 'TyVarBndrUnit' are simply type
-- synonyms for 'TyVarBndr', so making the functional dependencies
-- bidirectional would cause these instances to be rejected.
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

#if __GLASGOW_HASKELL__ >= 900
-- | This instance is only @flag@-polymorphic on GHC 9.0 or later, since
-- previous versions of GHC do not equip 'TyVarBndr' with a @flag@ type
-- parameter. As a result, we define two separate instances for 'DTyVarBndr'
-- on older GHCs:
--
-- @
-- instance 'Desugar' 'TyVarBndrSpec' 'DTyVarBndrSpec'
-- instance 'Desugar' 'TyVarBndrUnit' 'DTyVarBndrUnit'
-- @
instance Desugar (TyVarBndr flag) (DTyVarBndr flag) where
  desugar = dsTvb
  sweeten = tvbToTH
#else
-- | This instance monomorphizes the @flag@ parameter of 'DTyVarBndr' since
-- pre-9.0 versions of GHC do not equip 'TyVarBndr' with a @flag@ type
-- parameter. There is also a corresponding instance for
-- 'TyVarBndrUnit'/'DTyVarBndrUnit'.
instance Desugar TyVarBndrSpec DTyVarBndrSpec where
  desugar = dsTvbSpec
  sweeten = tvbToTH

-- | This instance monomorphizes the @flag@ parameter of 'DTyVarBndr' since
-- pre-9.0 versions of GHC do not equip 'TyVarBndr' with a @flag@ type
-- parameter. There is also a corresponding instance for
-- 'TyVarBndrSpec'/'DTyVarBndrSpec'.
instance Desugar TyVarBndrUnit DTyVarBndrUnit where
  desugar = dsTvbUnit
  sweeten = tvbToTH
#endif

instance Desugar [Dec] [DDec] where
  desugar = dsDecs
  sweeten = decsToTH

instance Desugar TypeArg DTypeArg where
  desugar = dsTypeArg
  sweeten = typeArgToTH

-- | If the declaration passed in is a 'DValD', creates new, equivalent
-- declarations such that the 'DPat' in all 'DValD's is just a plain
-- 'DVarPa'. Other declarations are passed through unchanged.
-- Note that the declarations that come out of this function are rather
-- less efficient than those that come in: they have many more pattern
-- matches.
flattenDValD :: Quasi q => DLetDec -> q [DLetDec]
flattenDValD dec@(DValD (DVarP _) _) = return [dec]
flattenDValD (DValD pat exp) = do
  x <- newUniqueName "x" -- must use newUniqueName here because we might be top-level
  let top_val_d = DValD (DVarP x) exp
      bound_names = F.toList $ extractBoundNamesDPat pat
  other_val_ds <- mapM (mk_val_d x) bound_names
  return $ top_val_d : other_val_ds
  where
    mk_val_d x name = do
      y <- newUniqueName "y"
      let pat'  = wildify name y pat
          match = DMatch pat' (DVarE y)
          cas   = DCaseE (DVarE x) [match]
      return $ DValD (DVarP name) cas

    wildify name y p =
      case p of
        DLitP lit -> DLitP lit
        DVarP n
          | n == name -> DVarP y
          | otherwise -> DWildP
        DConP con ts ps -> DConP con ts (map (wildify name y) ps)
        DTildeP pa -> DTildeP (wildify name y pa)
        DBangP pa -> DBangP (wildify name y pa)
        DSigP pa ty -> DSigP (wildify name y pa) ty
        DWildP -> DWildP

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
-- , DFunD y [ DClause [DConP X1 [DVarP field]] (DVarE field)
--           , DClause [DConP X2 [DVarP field]] (DVarE field) ] ]
-- @
--
-- instead of returning one binding for @X1@ and another binding for @X2@.
--
-- 'getRecordSelectors' does not attempt to filter out \"naughty\" record
-- selectors—that is, records whose field types mention existentially
-- quantified type variables that do not appear in the constructor's return
-- type. Here is an example of a naughty record selector:
--
-- @
-- data Some :: (Type -> Type) -> Type where
--   MkSome :: { getSome :: f a } -> Some f
-- @
--
-- GHC itself will not allow the use of @getSome@ as a top-level function due
-- to its type @f a@ mentioning the existential variable @a@, but
-- 'getRecordSelectors' will return it nonetheless. Ultimately, this design
-- choice is a practical one, as detecting which type variables are existential
-- in Template Haskell is difficult in the general case.
getRecordSelectors :: DsMonad q => [DCon] -> q [DLetDec]
getRecordSelectors cons = merge_let_decs `fmap` concatMapM get_record_sels cons
  where
    get_record_sels (DCon con_tvbs _ con_name con_fields con_ret_ty) =
      case con_fields of
        DRecC fields -> go fields
        DNormalC{}   -> return []
        where
          go fields = do
            varName <- qNewName "field"
            return $ concat
              [ [ DSigD name $ DForallT (DForallInvis con_tvbs)
                             $ DArrowT `DAppT` con_ret_ty `DAppT` field_ty
                , DFunD name [DClause [DConP con_name []
                                         (mk_field_pats n (length fields) varName)]
                                      (DVarE varName)] ]
              | ((name, _strict, field_ty), n) <- zip fields [0..]
              ]

    mk_field_pats :: Int -> Int -> Name -> [DPat]
    mk_field_pats 0 total name = DVarP name : (replicate (total-1) DWildP)
    mk_field_pats n total name = DWildP : mk_field_pats (n-1) (total-1) name

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
mkExtraDKindBinders :: forall q. DsMonad q => DKind -> q [DTyVarBndrUnit]
mkExtraDKindBinders k = do
  k' <- expandType k
  let (fun_args, _) = unravelDType k'
      vis_fun_args  = filterDVisFunArgs fun_args
  mapM mk_tvb vis_fun_args
  where
    mk_tvb :: DVisFunArg -> q DTyVarBndrUnit
    mk_tvb (DVisFADep tvb) = return tvb
    mk_tvb (DVisFAAnon ki) = DKindedTV <$> qNewName "a" <*> return () <*> return ki

{- $localReification

@template-haskell@ reification functions like 'reify' and 'qReify', as well as
@th-desugar@'s 'reifyWithWarning', only look through declarations that either
(1) have already been typechecked in the current module, or (2) are in scope
because of imports. We refer to this as /global/ reification. Sometimes,
however, you may wish to reify declarations that have been quoted but not
yet been typechecked, such as in the following example:

@
example :: IO ()
example = putStrLn
  $(do decs <- [d| data Foo = MkFoo |]
       info <- 'reify' (mkName \"Foo\")
       stringE $ pprint info)
@

Because @Foo@ only exists in a TH quote, it is not available globally. As a
result, the call to @'reify' (mkName \"Foo\")@ will fail.

To make this sort of example possible, @th-desugar@ extends global reification
with /local/ reification. A function that performs local reification (such
as 'dsReify', 'reifyWithLocals', or similar functions that have a 'DsMonad'
context) looks through both typechecked (or imported) declarations /and/ quoted
declarations that are currently in scope. One can add quoted declarations in
the current scope by using the 'withLocalDeclarations' function. Here is an
example of how to repair the example above using 'withLocalDeclarations':

@
example2 :: IO ()
example2 = putStrLn
  $(do decs <- [d| data Foo = MkFoo |]
       info <- 'withLocalDeclarations' decs $
                 'reifyWithLocals' (mkName \"Foo\")
       stringE $ pprint info)
@

Note that 'withLocalDeclarations' should only be used to add quoted
declarations with names that are not duplicates of existing global or local
declarations. Adding duplicate declarations through 'withLocalDeclarations'
is undefined behavior and should be avoided. This is unlikely to happen if
you are only using 'withLocalDeclarations' in conjunction with TH quotes,
however. For instance, this is /not/ an example of duplicate declarations:

@
data T = MkT1

$(do decs <- [d| data T = MkT2 |]
     info <- 'withLocalDeclarations' decs ...
     ...)
@

The quoted @data T = MkT2@ does not conflict with the top-level @data T = Mk1@
since declaring a data type within TH quotes gives it a fresh, unique name that
distinguishes it from any other data types already in scope.
-}
