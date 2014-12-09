{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.TH.Desugar.Context
    ( testContext
    , testInstances
    , magicHashName
    ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad.State (StateT, get, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhere, mkT, everywhereM, mkM)
import Data.List ({-dropWhileEnd,-} intercalate)
import Data.Map as Map (Map, lookup, insert)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Desugar.Reify as DS (DsMonad)
import Language.Haskell.TH.Desugar.Core as DS (dsType)
import qualified Language.Haskell.TH.Desugar.Expand as DS (expandType)
import Language.Haskell.TH.Desugar.Sweeten as DS (typeToTH)

-- We need these to use Pred as the key of a Map.
deriving instance Ord TyLit
deriving instance Ord Pred
deriving instance Ord TyVarBndr
deriving instance Ord Type

-- | Is this list of predicates satisfiable?  Find out using type
-- synonym expansion, variable substitution, elimination of vacuous
-- predicates, and unification.
--
-- Elements of the Pred type correspond to elements of the list to the
-- left of the @=>@ in a Haskell declaration.  These can either be
-- @ClassP@ values which represent superclasses, or @EqualP@ values
-- which represent the @~@ operator.
testContext :: DS.DsMonad m => ([Type] -> Bool) -> [Pred] -> StateT (Map Pred Bool) m Bool
testContext ok context =
    and <$> (mapM (consistent ok) =<< simplifyContext context)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: DS.DsMonad m => [Pred] -> StateT (Map Pred Bool) m [Pred]
simplifyContext context =
    do (expanded :: [Pred]) <- expandTypes context
       let (context' :: [Pred]) = concat $ map unify expanded
       let context'' = foldl testPredicate context' context'
       if (context'' == context) then return context'' else simplifyContext context''

-- | Try to simplify the context by eliminating of one of the predicates.
-- If we succeed start again with the new context.
testPredicate :: [Pred] -> Pred -> [Pred]
testPredicate context (EqualP v@(VarT _) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
testPredicate context (EqualP a v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
testPredicate context p@(EqualP a b) | a == b = filter (/= p) context
testPredicate context _ = context

expandTypes :: (Data a, DS.DsMonad m) => a -> StateT (Map Pred Bool) m a
expandTypes = everywhereM (mkM (lift . expandType))
    where
      expandType :: (Quasi m, DS.DsMonad m) => Type -> m Type
      expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expandType)

-- | Unify the two arguments of an EqualP predicate, return a list of
-- simpler predicates associating types with a variables.
unify :: Pred -> [Pred]
unify (EqualP (AppT a b) (AppT c d)) = unify (EqualP a c) ++ unify (EqualP b d)
unify (EqualP (ConT a) (ConT b)) | a == b = []
unify (EqualP a@(VarT _) b) = [EqualP a b]
unify (EqualP a b@(VarT _)) = [EqualP a b]
unify x = [x]

consistent :: DS.DsMonad m => ([Type] -> Bool) -> Pred -> StateT (Map Pred Bool) m Bool
consistent ok (ClassP cls args) = anyInstances ok cls args -- Do we need additional context here?
consistent ok (EqualP (AppT a b) (AppT c d)) = (&&) <$> consistent ok (EqualP a c) <*> consistent ok (EqualP b d)
consistent _ (EqualP (VarT _) _) = return True
consistent _ (EqualP _ (VarT _)) = return True
consistent _ (EqualP a b) | a == b = return True
consistent _ (EqualP _ _) = return False

-- | Is there a variable assignment for which this predicate is
-- satisfiable?  The Pred type looks like this:
--
--     data Pred = ClassP Name [Type] | EqualP Type Type
--
-- If we want to compute @testPredicates [ClassP Parsable [Maybe
-- Circuit]]@, we start by calling @qReifyInstances Parsable [Maybe
-- Circuit]@, which replies that that there is an instance @Parsable a
-- => Parsable (Maybe a)@.  However, we still don't know whether there
-- is an instance @Parsable Circuit@, so we don't yet know whether the
-- result should be True of False.  Therefore, we then need to
--
--  1. unify @Parsable (Maybe Circuit)@ with @Parsable (Maybe a)@, which gives us @Circuit ~ a@,
--
--  2. make that substitution into @Parsable a@, to get @Parsable Circuit@
--
--  3. test for instances of @Parsable Circuit@.
anyInstances :: DS.DsMonad m => ([Type] -> Bool) -> Name -> [Type] -> StateT (Map Pred Bool) m Bool -- [Dec]
-- If this is an unlifted type we can't call qReifyInstances (it will
-- get a kind error) but we want to indicate that the instance should
-- be used.  This is because I don't know how to properly generate an
-- instance for an unlifted type automatically.
anyInstances ok _ args | ok args = return True
-- Ask for matching instances for this list of types, then see whether
-- any of them can be unified with the instance context.
anyInstances ok cls argTypes =
    do let p = (ClassP cls argTypes)
       mp <- get
       case Map.lookup p mp of
         Just x -> return x
         Nothing -> do
           -- Add an entry with a bogus value to limit recursion on
           -- this predicate we are currently testing
           _ <- record cls argTypes False
           insts <- lift $ qReifyInstances cls argTypes
           r <- or <$> mapM (testInstance ok [] cls argTypes) insts
           -- Now insert the correct value into the map.
           _ <- record cls argTypes r
           -- st <- get
           -- trace (pprint' (ClassP cls argTypes) ++ " now in [" ++ intercalate ", " (map pprint' (keys (imp st))) ++ "]") (return ())
           -- trace ("anyInstances " ++ pprint' (ClassP cls argTypes) ++ " -> " ++ show r) (return ())
           return r

-- | This will usually recognize an unlifted type by convention.
magicHashName :: [Type] -> Bool
magicHashName [ConT (Name (OccName s) _)] = last s == '#'
magicHashName _ = False

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: DS.DsMonad m => ([Type] -> Bool) -> [Pred] -> Name -> [Type] -> InstanceDec -> StateT (Map Pred Bool) m Bool
testInstance ok oldContext cls argTypes (InstanceD newContext instType _) = do
  testContext ok (instancePredicates (reverse argTypes) instType ++ newContext ++ oldContext) >>= record cls argTypes
    where
      instancePredicates :: [Type] -> Type -> [Pred]
      instancePredicates (x : xs) (AppT l r) = EqualP x r : instancePredicates xs l
      instancePredicates [] (ConT cls') | cls == cls' = []
      instancePredicates _ _ = error $ "testInstance: Failure unifying instance with arguments.  This should never happen because qReifyInstance returned this instance for these exact arguments: argTypes=[" ++ intercalate ", " (map show argTypes) ++ "], instType=" ++ show instType
testInstance _ _ _ _ x = error $ "Unexpected InstanceDec.  If this happens there must be some new sort of instance declaration I wasn't expecting: " ++ show x

-- | Call testContext to see whether there are any usable instances
-- for the given class name and argument types.  The Map used by the
-- state monad is passed in for efficiency - we get the same result
-- more slowly if the empty map is used and discard the returned Map.
testInstances :: DS.DsMonad m => ([Type] -> Bool) -> Name -> [Type] -> Map Pred Bool -> m (Bool, Map Pred Bool)
testInstances ok className argumentTypes mp =
    runStateT (let p = ClassP className argumentTypes in testContext ok [p] >>= record className argumentTypes) mp

record :: Monad m => Name -> [Type] -> Bool -> StateT (Map Pred Bool) m Bool
record cls types result = modify (Map.insert (ClassP cls types) result) >> return result
