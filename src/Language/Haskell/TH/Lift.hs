{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.Haskell.TH.Lift (deriveLift, deriveLiftMany, deriveLift', deriveLiftMany', Lift(..)) where

#if !(MIN_VERSION_template_haskell(2,4,0))
import Data.PackedString (PackedString, packString, unpackPS)
#endif /* MIN_VERSION_template_haskell(2,4,0) */

#if !(MIN_VERSION_template_haskell(2,10,0))
import GHC.Exts
#endif /* !(MIN_VERSION_template_haskell(2,10,0)) */
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Control.Monad ((<=<))

modName :: String
modName = "Language.Haskell.TH.Lift"

-- | Derive Lift instances for the given datatype.
deriveLift :: Name -> Q [Dec]
deriveLift = deriveLift' <=< reify

-- | Derive Lift instances for many datatypes.
deriveLiftMany :: [Name] -> Q [Dec]
deriveLiftMany = deriveLiftMany' <=< mapM reify

-- | Obtain Info values through a custom reification function. This is useful
-- when generating instances for datatypes that have not yet been declared.
deriveLift' :: Info -> Q [Dec]
deriveLift' = fmap (:[]) . deriveLiftOne

deriveLiftMany' :: [Info] -> Q [Dec]
deriveLiftMany' = mapM deriveLiftOne

deriveLiftOne :: Info -> Q Dec
deriveLiftOne i =
  case i of
    TyConI (DataD dcx n vsk cons _) ->
      liftInstance dcx n (map unTyVarBndr vsk) (map doCons cons)
    TyConI (NewtypeD dcx n vsk con _) ->
      liftInstance dcx n (map unTyVarBndr vsk) [doCons con]
    _ -> error (modName ++ ".deriveLift: unhandled: " ++ pprint i)
  where liftInstance dcx n vs cases =
          instanceD (ctxt dcx vs)
                    (conT ''Lift `appT` typ n (map fst vs))
                    [funD 'lift cases]
        typ n = foldl appT (conT n) . map varT
        ctxt dcx = fmap (dcx ++) . cxt . concatMap liftPred
        -- Only consider *-kinded type variables, because Lift instances cannot
        -- meaningfully be given to types of other kinds.
#if MIN_VERSION_template_haskell(2,10,0)
        unTyVarBndr (PlainTV v) = (v, StarT)
        unTyVarBndr (KindedTV v k) = (v, k)
        liftPred (v, StarT) = [conT ''Lift `appT` varT v]
        liftPred (_, _) = []
#elif MIN_VERSION_template_haskell(2,8,0)
        unTyVarBndr (PlainTV v) = (v, StarT)
        unTyVarBndr (KindedTV v k) = (v, k)
        liftPred (v, StarT) = [classP ''Lift [varT v]]
        liftPred (_, _) = []
#elif MIN_VERSION_template_haskell(2,4,0)
        unTyVarBndr (PlainTV v) = (v, StarK)
        unTyVarBndr (KindedTV v k) = (v, k)
        liftPred (v, StarK) = [classP ''Lift [varT v]]
        liftPred (_, _) = []
#else /* template-haskell < 2.4.0 */
        unTyVarBndr v = v
        liftPred n = conT ''Lift `appT` varT n
#endif

doCons :: Con -> Q Clause
doCons (NormalC c sts) = do
  let ns = zipWith (\_ i -> "x" ++ show (i :: Int)) sts [0..]
      con = [| conE c |]
      args = [ [| lift $(varE (mkName n)) |] | n <- ns ]
      e = foldl (\e1 e2 -> [| appE $e1 $e2 |]) con args
  clause [conP c (map (varP . mkName) ns)] (normalB e) []
doCons (RecC c sts) = doCons $ NormalC c [(s, t) | (_, s, t) <- sts]
doCons (InfixC _sty1 c _sty2) = do
  let con = [| conE c |]
      left = [| lift $(varE (mkName "x0")) |]
      right = [| lift $(varE (mkName "x1")) |]
      e = [| infixApp $left $con $right |]
  clause [infixP (varP (mkName "x0")) c (varP (mkName "x1"))] (normalB e) []
doCons (ForallC _ _ c) = doCons c

instance Lift Name where
    lift (Name occName nameFlavour) = [| Name occName nameFlavour |]

#if MIN_VERSION_template_haskell(2,4,0)
instance Lift OccName where
  lift n = [| mkOccName $(lift $ occString n) |]

instance Lift PkgName where
  lift n = [| mkPkgName $(lift $ pkgString n) |]

instance Lift ModName where
  lift n = [| mkModName $(lift $ modString n) |]

#else /* MIN_VERSION_template_haskell(2,4,0) */
instance Lift PackedString where
  lift ps = [| packString $(lift $ unpackPS ps) |]

#endif /* MIN_VERSION_template_haskell(2,4,0) */
instance Lift NameFlavour where
    lift NameS = [| NameS |]
    lift (NameQ modnam) = [| NameQ modnam |]
#if MIN_VERSION_template_haskell(2,10,0)
    lift (NameU i) = [| NameU i |]
    lift (NameL i) = [| NameL i |]
#else /* MIN_VERSION_template_haskell(2,10,0) */
    lift (NameU i) = [| case $( lift (I# i) ) of
                            I# i' -> NameU i' |]
    lift (NameL i) = [| case $( lift (I# i) ) of
                            I# i' -> NameL i' |]
#endif /* MIN_VERSION_template_haskell(2,10,0) */
    lift (NameG nameSpace pkgName modnam)
     = [| NameG nameSpace pkgName modnam |]

instance Lift NameSpace where
    lift VarName = [| VarName |]
    lift DataName = [| DataName |]
    lift TcClsName = [| TcClsName |]

-- These instances should really go in the template-haskell package.

instance Lift () where
  lift _ = [| () |]

instance Lift Rational where
  lift x = return (LitE (RationalL x))
