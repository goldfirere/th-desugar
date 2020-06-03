{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE TypeInType #-}
#endif
#if __GLASGOW_HASKELL__ >= 806
{-# LANGUAGE StarIsType #-}
#endif
#if __GLASGOW_HASKELL__ >= 809
{-# LANGUAGE CUSKs #-}
#endif
-- This is kept in a separate module from ReifyTypeSigs to isolate the use of
-- the -XCUSKs language extension.
module ReifyTypeCUSKs where

#if __GLASGOW_HASKELL__ >= 800 && __GLASGOW_HASKELL__ < 806
import Data.Kind (type (*))
#endif
#if __GLASGOW_HASKELL__ < 710
import Data.Traversable (traverse)
#endif
import GHC.Exts (Constraint)
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Syntax
import Splices (eqTH)

test_reify_type_cusks, test_reify_type_no_cusks :: [Bool]
(test_reify_type_cusks, test_reify_type_no_cusks) =
  $(do cusk_decls <-
         [d| data A1 (a :: *)
             type A2 (a :: *) = (a :: *)
             type family A3 a
             data family A4 a
             type family A5 (a :: *) :: * where
               A5 a = a
             class A6 (a :: *) where
               type A7 a b

#if __GLASGOW_HASKELL__ >= 800
             data A8 (a :: k) :: k -> *
#endif
#if __GLASGOW_HASKELL__ >= 804
             data A9 (a :: j) :: forall k. k -> *
#endif
#if __GLASGOW_HASKELL__ >= 809
             data A10 (k :: Type) (a :: k)
             data A11 :: forall k -> k -> *
#endif
           |]

       no_cusk_decls <-
         [d| data B1 a
             type B2 (a :: *) = a
             type B3 a = (a :: *)
             type family B4 (a :: *) where
               B4 a = a
             type family B5 a :: * where
               B5 a = a
             class B6 a where
               type B7 (a :: *) (b :: *) :: *

#if __GLASGOW_HASKELL__ >= 800
             data B8 :: k -> *
#endif
#if __GLASGOW_HASKELL__ >= 804
             data B9 :: forall j. j -> k -> *
#endif
           |]

       let test_reify_kind :: DsMonad q
                           => String -> (Int, Maybe DKind) -> q Bool
           test_reify_kind prefix (i, expected_kind) = do
             actual_kind <- dsReifyType $ mkName $ prefix ++ show i
             return $ expected_kind `eqTH` actual_kind

           typeKind :: DKind
           typeKind = DConT typeKindName

           type_to_type :: DKind
           type_to_type = DArrowT `DAppT` typeKind `DAppT` typeKind

       cusk_decl_bools <-
         withLocalDeclarations cusk_decls $
         traverse (\(i, k) -> test_reify_kind "A" (i, Just k)) $
           [ (1, type_to_type)
           , (2, type_to_type)
           , (3, type_to_type)
           , (4, type_to_type)
           , (5, type_to_type)
           , (6, DArrowT `DAppT` typeKind `DAppT` DConT ''Constraint)
           , (7, DArrowT `DAppT` typeKind `DAppT` type_to_type)
           ]
#if __GLASGOW_HASKELL__ >= 800
           ++
           [ (8, let k = mkName "k" in
                 DForallT (DForallInvis [DPlainTV k SpecifiedSpec]) $
                 DArrowT `DAppT` DVarT k `DAppT`
                   (DArrowT `DAppT` DVarT k `DAppT` typeKind))
           ]
#endif
#if __GLASGOW_HASKELL__ >= 804
           ++
           [ (9, let j = mkName "j"
                     k = mkName "k" in
                 DForallT (DForallInvis [DPlainTV j SpecifiedSpec]) $
                 DArrowT `DAppT` DVarT j `DAppT`
                   (DForallT (DForallInvis [DPlainTV k SpecifiedSpec]) $
                    DArrowT `DAppT` DVarT k `DAppT` typeKind))
           ]
#endif
#if __GLASGOW_HASKELL__ >= 809
           ++
           [ (10, let k = mkName "k" in
                  DForallT (DForallVis [DKindedTV k () typeKind]) $
                  DArrowT `DAppT` DVarT k `DAppT` typeKind)
           , (11, let k = mkName "k" in
                  DForallT (DForallVis [DPlainTV k ()]) $
                  DArrowT `DAppT` DVarT k `DAppT` typeKind)
           ]
#endif

       no_cusk_decl_bools <-
         withLocalDeclarations no_cusk_decls $
         traverse (test_reify_kind "B") $
           map (, Nothing) $
                [1..7]
#if __GLASGOW_HASKELL__ >= 800
             ++ [8]
#endif
#if __GLASGOW_HASKELL__ >= 804
             ++ [9]
#endif
       lift (cusk_decl_bools, no_cusk_decl_bools))
