
module Language.Haskell.TH.Lift where

import GHC.Exts
import Data.PackedString
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

modName :: String
modName = "Language.Haskell.TH.Lift"

deriveLift :: Name -> Q Dec
deriveLift n
 = do i <- reify n
      case i of
          TyConI (DataD _ _ vs cons _) ->
              let ctxt = cxt [conT ''Lift `appT` varT v | v <- vs]
                  typ = foldl appT (conT n) $ map varT vs
                  fun = funD 'lift (map doCons cons)
              in instanceD ctxt (conT ''Lift `appT` typ) [fun]
          _ -> error (modName ++ ".deriveLift: unhandled: " ++ pprint i)

doCons :: Con -> Q Clause
doCons (NormalC c sts)
 = do let ns = zipWith (\_ i -> "x" ++ show i) sts [0..]
          con = [| conE c |]
          args = [ [| lift $(varE (mkName n)) |] | n <- ns ]
          e = foldl (\e1 e2 -> [| appE $e1 $e2 |]) con args
      clause [conP c (map (varP . mkName) ns)] (normalB e) []
doCons c = error (modName ++ ".doCons: Unhandled constructor: " ++ pprint c)

instance Lift Name where
    lift (Name occName nameFlavour) = [| Name occName nameFlavour |]

instance Lift PackedString where
    lift ps = [| packString $(lift $ unpackPS ps) |]

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

