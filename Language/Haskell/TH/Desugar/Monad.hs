{- Language/Haskell/TH/Desugar/Monad.hs

(c) Richard Eisenberg 2014
eir@cis.upenn.edu

Defines a desugaring monad class, capable of storing local declarations for
aid in reification.
-}

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.Haskell.TH.Desugar.Monad (
  DsMonad(..), DsM, withLocalDeclarations
  ) where

import Language.Haskell.TH.Syntax hiding ( lift )
import Control.Applicative
import Control.Monad.Reader

class Quasi m => DsMonad m where
  localDeclarations :: m [Dec]

instance DsMonad Q where
  localDeclarations = return []
instance DsMonad IO where
  localDeclarations = return []

newtype DsM q a = DsM (ReaderT [Dec] q a)
  deriving (Functor, Applicative, Monad, MonadTrans)
instance Quasi q => DsMonad (DsM q) where
  localDeclarations = DsM ask

withLocalDeclarations :: [Dec] -> DsM q a -> q a
withLocalDeclarations decs (DsM x) = runReaderT x decs

instance Quasi q => Quasi (DsM q) where
  qNewName          = lift `comp1` qNewName
  qReport           = lift `comp2` qReport
  qLookupName       = lift `comp2` qLookupName
  qReify            = lift `comp1` qReify
  qReifyInstances   = lift `comp2` qReifyInstances
  qLocation         = lift qLocation
  qRunIO            = lift `comp1` qRunIO
  qAddDependentFile = lift `comp1` qAddDependentFile
  qReifyRoles       = lift `comp1` qReifyRoles
  qReifyAnnotations = lift `comp1` qReifyAnnotations
  qReifyModule      = lift `comp1` qReifyModule
  qAddTopDecls      = lift `comp1` qAddTopDecls
  qAddModFinalizer  = lift `comp1` qAddModFinalizer
  qGetQ             = lift qGetQ
  qPutQ             = lift `comp1` qPutQ

  qRecover (DsM handler) (DsM body) = DsM $ do
    env <- ask
    lift $ qRecover (runReaderT handler env) (runReaderT body env)

-- helper functions for composition
comp1 :: (b -> c) -> (a -> b) -> a -> c
comp1 = (.)

comp2 :: (c -> d) -> (a -> b -> c) -> a -> b -> d
comp2 f g a b = f (g a b)
