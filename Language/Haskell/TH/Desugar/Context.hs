{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.TH.Desugar.Context
    ( instances
    , testInstance
    , testContext
    , expandTypes
    ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad (filterM)
import Control.Monad.State (MonadState, StateT(StateT), get, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhere, mkT, everywhereM, mkM)
import Data.List ({-dropWhileEnd,-} intercalate)
import Data.Map as Map (Map, lookup, insert)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Desugar.Reify as DS (DsMonad(localDeclarations))
import Language.Haskell.TH.Desugar.Core as DS (dsType)
import qualified Language.Haskell.TH.Desugar.Expand as DS (expandType)
import Language.Haskell.TH.Desugar.Sweeten as DS (typeToTH)

-- We need these to use Pred as the key of a Map.
deriving instance Ord TyLit
deriving instance Ord Pred
deriving instance Ord TyVarBndr
deriving instance Ord Type

instance Quasi m => Quasi (StateT s m) where
  qNewName  	    = lift . qNewName
  qReport a b  	    = lift $ qReport a b
  qRecover m1 m2    = StateT $ \ s -> runStateT m1 s `qRecover` runStateT m2 s
  qLookupName a b   = lift $ qLookupName a b
  qReify    	    = lift . qReify
  qReifyInstances a b = lift $ qReifyInstances a b
  qLocation 	    = lift qLocation
  qRunIO    	    = lift . qRunIO
  qAddDependentFile = lift . qAddDependentFile
#if MIN_VERSION_template_haskell(2,9,0)
  qReifyRoles       = lift . qReifyRoles
  qReifyAnnotations = lift . qReifyAnnotations
  qReifyModule      = lift . qReifyModule
  qAddTopDecls      = lift . qAddTopDecls
  qAddModFinalizer  = lift . qAddModFinalizer
  qGetQ             = lift qGetQ
  qPutQ             = lift . qPutQ
#endif

instance DsMonad m => DsMonad (StateT s m) where
    localDeclarations = lift localDeclarations

-- | Look up all the instances that match the given class name and
-- argument types, return only the ones (if any) that satisfy all the
-- instance context predicates.
instances :: (DS.DsMonad m, MonadState (Map Pred [InstanceDec]) m) => Name -> [Type] -> m [InstanceDec]
-- Ask for matching instances for this list of types, then see whether
-- any of them can be unified with the instance context.
instances cls argTypes =
    do p <- expandTypes (ClassP cls argTypes)
       mp <- get
       case Map.lookup p mp of
         Just x -> return x
         Nothing -> do
           -- Add an entry with a bogus value to limit recursion on
           -- the predicate we are currently testing
           modify (Map.insert p [])
           insts <- qReifyInstances cls argTypes
           r <- filterM (testInstance cls argTypes) insts
           -- Now insert the correct value into the map.
           modify (Map.insert p r)
           return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: (DS.DsMonad m, MonadState (Map Pred [InstanceDec]) m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance cls argTypes (InstanceD newContext instType _) = do
  testContext (instancePredicates (reverse argTypes) instType ++ newContext)
    where
      instancePredicates :: [Type] -> Type -> [Pred]
      instancePredicates (x : xs) (AppT l r) = EqualP x r : instancePredicates xs l
      instancePredicates [] (ConT cls') | cls == cls' = []
      instancePredicates _ _ = error $ (unlines ["testInstance: Failure unifying instance with arguments.  This should never",
                                                 "happen because qReifyInstance returned this instance for these exact arguments:",
                                                 " argTypes=[" ++ intercalate ", " (map show argTypes) ++ "]",
                                                 " instType=" ++ show instType])
testInstance _ _ x = error $ "Unexpected InstanceDec.  If this happens there must be some new sort of instance declaration I wasn't expecting: " ++ show x

-- | Is this list of predicates satisfiable?  Find out using type
-- synonym expansion, variable substitution, elimination of vacuous
-- predicates, and unification.
--
-- Elements of the Pred type correspond to elements of the list to the
-- left of the @=>@ in a Haskell declaration.  These can either be
-- @ClassP@ values which represent superclasses, or @EqualP@ values
-- which represent the @~@ operator.
testContext :: (DS.DsMonad m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m Bool
testContext context =
    and <$> (mapM consistent =<< simplifyContext context)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (DS.DsMonad m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m [Pred]
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

expandTypes :: (DsMonad m, Data a) => a -> m a
expandTypes = everywhereM (mkM expandType)

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

consistent :: (DS.DsMonad m, MonadState (Map Pred [InstanceDec]) m) => Pred -> m Bool
consistent (ClassP cls args) = (not . null) <$> instances cls args -- Do we need additional context here?
consistent (EqualP (AppT a b) (AppT c d)) = (&&) <$> consistent (EqualP a c) <*> consistent (EqualP b d) -- I'm told this is incorrect in the presence of type functions
consistent (EqualP (VarT _) _) = return True
consistent (EqualP _ (VarT _)) = return True
consistent (EqualP a b) | a == b = return True
consistent (EqualP _ _) = return False
