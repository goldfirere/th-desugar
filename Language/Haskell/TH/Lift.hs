module Language.Haskell.TH.Lift (deriveLift, deriveLiftWith, Lift(..)) where

import GHC.Exts
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

modName :: String
modName = "Language.Haskell.TH.Lift"

-- | Derive Lift instances for the given datatype.
deriveLift :: Name -> Q [Dec]
deriveLift = deriveLiftWith reify

-- | Obtain Info values through a custom reification function. This is useful
-- when generating instances for datatypes that have not yet been declared.
deriveLiftWith :: (Name -> Q Info) -> Name -> Q [Dec]
deriveLiftWith n = do
  i <- reify n
  case i of
    TyConI (DataD _ _ vsk cons _) ->
      liftInstance (map unTyVarBndr vsk) (map doCons cons)
    TyConI (NewtypeD _ _ vsk con _) ->
      liftInstance (map unTyVarBndr vsk) [doCons con]
    _ -> error (modName ++ ".deriveLift: unhandled: " ++ pprint i)
    where liftInstance vs cases =
            fmap (:[]) $ instanceD (ctxt vs) (conT ''Lift `appT` typ vs) [funD 'lift cases]
          unTyVarBndr (PlainTV v) = v
          unTyVarBndr (KindedTV v _) = v
          ctxt = cxt . map (\n -> classP ''Lift [varT n])
          typ = foldl appT (conT n) . map varT

doCons :: Con -> Q Clause
doCons (NormalC c sts) = do
  let ns = zipWith (\_ i -> "x" ++ show i) sts [0..]
      con = [| conE c |]
      args = [ [| lift $(varE (mkName n)) |] | n <- ns ]
      e = foldl (\e1 e2 -> [| appE $e1 $e2 |]) con args
  clause [conP c (map (varP . mkName) ns)] (normalB e) []
doCons (RecC c sts) = doCons $ NormalC c [(s, t) | (_, s, t) <- sts]
doCons (InfixC sty1 c sty2) = do
  let con = [| conE c |]
      left = [| lift $(varE (mkName "x0")) |]
      right = [| lift $(varE (mkName "x1")) |]
      e = [| infixApp $left $con $right |]
  clause [infixP (varP (mkName "x0")) c (varP (mkName "x1"))] (normalB e) []
doCons c = error (modName ++ ".doCons: Unhandled constructor: " ++ pprint c)

instance Lift Name where
    lift (Name occName nameFlavour) = [| Name occName nameFlavour |]

instance Lift OccName where
  lift n = [| mkOccName $(lift $ occString n) |]

instance Lift PkgName where
  lift n = [| mkPkgName $(lift $ pkgString n) |]

instance Lift ModName where
  lift n = [| mkModName $(lift $ modString n) |]

instance Lift NameFlavour where
    lift NameS = [| NameS |]
    lift (NameQ modName) = [| NameQ modName |]
    lift (NameU i) = [| case $( lift (I# i) ) of
                            I# i' -> NameU i' |]
    lift (NameL i) = [| case $( lift (I# i) ) of
                            I# i' -> NameL i' |]
    lift (NameG nameSpace pkgName modName)
     = [| NameG nameSpace pkgName modName |]

instance Lift NameSpace where
    lift VarName = [| VarName |]
    lift DataName = [| DataName |]
    lift TcClsName = [| TcClsName |]

-- These instances should really go in the template-haskell package.

instance Lift () where
  lift _ = [| () |]

instance Lift Rational where
  lift x = return (LitE (RationalL x))
