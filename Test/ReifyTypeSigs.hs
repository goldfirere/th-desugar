{-# LANGUAGE CPP #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
#if __GLASGOW_HASKELL__ >= 809
{-# LANGUAGE StandaloneKindSignatures #-}
#endif
module ReifyTypeSigs where

#if __GLASGOW_HASKELL__ >= 809
import Data.Kind
import Data.Proxy
#endif
#if __GLASGOW_HASKELL__ < 710
import Data.Traversable (traverse)
#endif
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Syntax hiding (Type)
import Splices (eqTH)

test_reify_kind_sigs :: [Bool]
test_reify_kind_sigs =
  $(do kind_sig_decls <-
         [d|
#if __GLASGOW_HASKELL__ >= 809
             type A1 :: forall k. k -> Type
             data A1 a

             type A2 :: k -> Type
             type A2 a = a

             type A3 :: forall k. k -> Type
             type family A3

             type A4 :: forall k. k -> Type
             data family A4 a

             type A5 :: k -> Type
             type family A5 a where
               A5 a = a

             type A6 :: forall (k :: Bool) -> Proxy k -> Constraint
             class A6 a b where
               type A7 a c
#endif
           |]

       let test_reify_kind :: DsMonad q
                           => (Int, DKind) -> q Bool
           test_reify_kind (i, expected_kind) = do
             actual_kind <- dsReifyType $ mkName $ "A" ++ show i
             return $ Just expected_kind `eqTH` actual_kind

       kind_sig_decl_bools <-
         withLocalDeclarations kind_sig_decls $
         traverse test_reify_kind $
           []
#if __GLASGOW_HASKELL__ >= 809
           ++
           let k = mkName "k"
               typeKind = DConT typeKindName
               boolKind = DConT ''Bool
               k_to_type = DArrowT `DAppT` DVarT k `DAppT` typeKind
               forall_k_invis_k_to_type =
                 DForallT (DForallInvis [DPlainTV k SpecifiedSpec]) k_to_type in
           [ (1, forall_k_invis_k_to_type)
           , (2, k_to_type)
           , (3, forall_k_invis_k_to_type)
           , (4, forall_k_invis_k_to_type)
           , (5, k_to_type)
           , (6, DForallT (DForallVis [DKindedTV k () boolKind]) $
                 DArrowT `DAppT` (DConT ''Proxy `DAppT` DVarT k)
                         `DAppT` DConT ''Constraint)
           , (7, DArrowT `DAppT` boolKind `DAppT`
                   (DArrowT `DAppT` typeKind `DAppT` typeKind))
           ]
#endif

       lift kind_sig_decl_bools)
