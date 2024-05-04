{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE TemplateHaskell, UnboxedTuples, ParallelListComp, CPP,
             RankNTypes, TypeFamilies,
             DataKinds, ConstraintKinds, PolyKinds, MultiParamTypeClasses,
             FlexibleInstances, ExistentialQuantification,
             ScopedTypeVariables, GADTs, ViewPatterns, TupleSections,
             TypeOperators, PartialTypeSignatures, PatternSynonyms,
             TypeApplications, MagicHash #-}
{-# OPTIONS -Wno-incomplete-patterns -Wno-overlapping-patterns
            -Wno-unused-matches -Wno-type-defaults
            -Wno-missing-signatures -Wno-unused-do-bind
            -Wno-missing-fields -Wno-incomplete-record-updates
            -Wno-partial-type-signatures -Wno-redundant-constraints #-}

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
#endif

#if __GLASGOW_HASKELL__ < 806
{-# LANGUAGE TypeInType #-}
#endif

#if __GLASGOW_HASKELL__ >= 809
{-# LANGUAGE StandaloneKindSignatures #-}
#endif

#if __GLASGOW_HASKELL__ >= 906
{-# LANGUAGE TypeData #-}
#endif

#if __GLASGOW_HASKELL__ >= 907
{-# LANGUAGE TypeAbstractions #-}
#endif

#if __GLASGOW_HASKELL__ >= 909
{-# LANGUAGE RequiredTypeArguments #-}
#endif

module Main where

import Prelude hiding ( exp )

import Test.HUnit
import Test.Hspec hiding ( runIO )
-- import Test.Hspec.HUnit

import Splices
import qualified DsDec
import qualified Dec
import Dec ( RecordSel )
import ReifyTypeCUSKs
import ReifyTypeSigs
import T159Decs ( t159A, t159B )
import T183 ( t183 )
import qualified Language.Haskell.TH.Datatype.TyVarBndr as THAbs
import Language.Haskell.TH.Desugar
import qualified Language.Haskell.TH.Desugar.OSet as OS
import Language.Haskell.TH.Desugar.Expand  ( expandUnsoundly )
import Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax as Syn

import Control.Exception ( ErrorCall )
import Control.Monad

import qualified Data.Map as M
import Data.Proxy

#if __GLASGOW_HASKELL__ >= 900
import Prelude as P
#endif

#if __GLASGOW_HASKELL__ >= 906
import GHC.Tuple ( Solo(MkSolo) )
#elif __GLASGOW_HASKELL__ >= 900
import GHC.Tuple ( Solo(Solo) )
#endif

#if __GLASGOW_HASKELL__ >= 908
import qualified FakeTuples
import GHC.Tuple ( Tuple0, Tuple1, Tuple2, Tuple3, Unit )
#endif

#if __GLASGOW_HASKELL__ >= 910
import qualified FakeSums
import GHC.Types (Solo#, Sum2#, Sum3#, Sum4#, Tuple0#, Tuple1#, Tuple2#, Tuple3#, Unit#)
#endif

-- |
-- Convert a HUnit test suite to a spec.  This can be used to run existing
-- HUnit tests with Hspec.
fromHUnitTest :: Test -> Spec
-- copied from https://github.com/hspec/hspec/blob/master/hspec-contrib/src/Test/Hspec/Contrib/HUnit.hs
fromHUnitTest t = case t of
  TestList xs -> mapM_ go xs
  x -> go x
  where
    go :: Test -> Spec
    go t_ = case t_ of
      TestLabel s (TestCase e) -> it s e
      TestLabel s (TestList xs) -> describe s (mapM_ go xs)
      TestLabel s x -> describe s (go x)
      TestList xs -> describe "<unlabeled>" (mapM_ go xs)
      TestCase e -> it "<unlabeled>" e

tests :: Test
tests = test [ "sections" ~: $test1_sections  @=? $(dsSplice test1_sections)
             , "lampats"  ~: $test2_lampats   @=? $(dsSplice test2_lampats)
             , "lamcase"  ~: $test3_lamcase   @=? $(dsSplice test3_lamcase)
-- Must fix nested pattern-matching for this to work. Argh.
--           , "tuples"   ~: $test4_tuples    @=? $(dsSplice test4_tuples)
             , "ifs"      ~: $test5_ifs       @=? $(dsSplice test5_ifs)
             , "ifs2"     ~: $test6_ifs2      @=? $(dsSplice test6_ifs2)
             , "let"      ~: $test7_let       @=? $(dsSplice test7_let)
             , "case"     ~: $test8_case      @=? $(dsSplice test8_case)
             , "do"       ~: $test9_do        @=? $(dsSplice test9_do)
             , "comp"     ~: $test10_comp     @=? $(dsSplice test10_comp)
             , "parcomp"  ~: $test11_parcomp  @=? $(dsSplice test11_parcomp)
             , "parcomp2" ~: $test12_parcomp2 @=? $(dsSplice test12_parcomp2)
             , "sig"      ~: $test13_sig      @=? $(dsSplice test13_sig)
             , "record"   ~: $test14_record   @=? $(dsSplice test14_record)
             , "litp"     ~: $test15_litp     @=? $(dsSplice test15_litp)
             , "tupp"     ~: $test16_tupp     @=? $(dsSplice test16_tupp)
             , "infixp"   ~: $test17_infixp   @=? $(dsSplice test17_infixp)
             , "tildep"   ~: $test18_tildep   @=? $(dsSplice test18_tildep)
             , "bangp"    ~: $test19_bangp    @=? $(dsSplice test19_bangp)
             , "asp"      ~: $test20_asp      @=? $(dsSplice test20_asp)
             , "wildp"    ~: $test21_wildp    @=? $(dsSplice test21_wildp)
             , "listp"    ~: $test22_listp    @=? $(dsSplice test22_listp)
#if __GLASGOW_HASKELL__ >= 801
             , "sigp"     ~: $test23_sigp     @=? $(dsSplice test23_sigp)
#endif
             , "fun"      ~: $test24_fun      @=? $(dsSplice test24_fun)
             , "fun2"     ~: $test25_fun2     @=? $(dsSplice test25_fun2)
             , "forall"   ~: $test26_forall   @=? $(dsSplice test26_forall)
             , "kisig"    ~: $test27_kisig    @=? $(dsSplice test27_kisig)
             , "tupt"     ~: $test28_tupt     @=? $(dsSplice test28_tupt)
             , "listt"    ~: $test29_listt    @=? $(dsSplice test29_listt)
             , "promoted" ~: $test30_promoted @=? $(dsSplice test30_promoted)
             , "constraint" ~: $test31_constraint @=? $(dsSplice test31_constraint)
             , "tylit"    ~: $test32_tylit    @=? $(dsSplice test32_tylit)
             , "tvbs"     ~: $test33_tvbs     @=? $(dsSplice test33_tvbs)
             , "let_as"   ~: $test34_let_as   @=? $(dsSplice test34_let_as)
             , "pred"     ~: $test37_pred     @=? $(dsSplice test37_pred)
             , "pred2"    ~: $test38_pred2    @=? $(dsSplice test38_pred2)
             , "eq"       ~: $test39_eq       @=? $(dsSplice test39_eq)
             , "wildcard" ~: $test40_wildcards@=? $(dsSplice test40_wildcards)
#if __GLASGOW_HASKELL__ >= 801
             , "typeapps"   ~: $test41_typeapps   @=? $(dsSplice test41_typeapps)
             , "scoped_tvs" ~: $test42_scoped_tvs @=? $(dsSplice test42_scoped_tvs)
             , "ubx_sums"   ~: $test43_ubx_sums   @=? $(dsSplice test43_ubx_sums)
#endif
             , "let_pragma" ~: $test44_let_pragma @=? $(dsSplice test44_let_pragma)
--             , "empty_rec"  ~: $test45_empty_record_con @=? $(dsSplice test45_empty_record_con)
        -- This one can't be tested by this means, because it contains an "undefined"
#if __GLASGOW_HASKELL__ >= 803
             , "over_label" ~: $test46_overloaded_label @=? $(dsSplice test46_overloaded_label)
#endif
             , "do_partial_match" ~: $test47_do_partial_match @=? $(dsSplice test47_do_partial_match)
#if __GLASGOW_HASKELL__ >= 805
             , "quantified_constraints" ~: $test48_quantified_constraints @=? $(dsSplice test48_quantified_constraints)
#endif
#if __GLASGOW_HASKELL__ >= 807
             , "implicit_params" ~: $test49_implicit_params @=? $(dsSplice test49_implicit_params)
             , "vka"             ~: $test50_vka             @=? $(dsSplice test50_vka)
#endif
#if __GLASGOW_HASKELL__ >= 809
             , "tuple_sections"  ~: $test51_tuple_sections  @=? $(dsSplice test51_tuple_sections)
#endif
#if __GLASGOW_HASKELL__ >= 900
             , "qual_do"         ~: $test52_qual_do         @=? $(dsSplice test52_qual_do)
#endif
#if __GLASGOW_HASKELL__ >= 901
             , "vta_in_con_pats" ~: $test53_vta_in_con_pats @=? $(dsSplice test53_vta_in_con_pats)
#endif
#if __GLASGOW_HASKELL__ >= 902
             , "overloaded_record_dot" ~: $test54_overloaded_record_dot @=? $(dsSplice test54_overloaded_record_dot)
#endif
#if __GLASGOW_HASKELL__ >= 903
             , "opaque_pragma" ~: $test55_opaque_pragma @=? $(dsSplice test55_opaque_pragma)
             , "lambda_cases" ~: $test56_lambda_cases @=? $(dsSplice test56_lambda_cases)
#endif
#if __GLASGOW_HASKELL__ >= 907
             , "typed_th_bracket" ~: $$($test57_typed_th_bracket) @=? $$($(dsSplice test57_typed_th_bracket))
             , "typed_th_splice" ~: $test58_typed_th_splice @=? $(dsSplice test58_typed_th_splice)
#endif
#if __GLASGOW_HASKELL__ >= 909
             , "embedded_types_keyword" ~: $test59_embedded_types_keyword @=? $(dsSplice test59_embedded_types_keyword)
             , "embedded_types_no_keyword" ~: $test60_embedded_types_no_keyword @=? $(dsSplice test60_embedded_types_no_keyword)
             , "invis_type_pat" ~: $test61_invis_type_pat @=? $(dsSplice test61_invis_type_pat)
             , "embedded_types_lambda_keyword" ~: $test62_embedded_types_lambda_keyword @=? $(dsSplice test62_embedded_types_lambda_keyword)
             , "embedded_types_case_keyword" ~: $test63_embedded_types_case_keyword @=? $(dsSplice test63_embedded_types_case_keyword)
             , "embedded_types_cases_keyword" ~: $test64_embedded_types_cases_keyword @=? $(dsSplice test64_embedded_types_cases_keyword)
             , "embedded_types_lambda_no_keyword" ~: $test65_embedded_types_lambda_no_keyword @=? $(dsSplice test65_embedded_types_lambda_no_keyword)
             , "embedded_types_case_no_keyword" ~: $test66_embedded_types_case_no_keyword @=? $(dsSplice test66_embedded_types_case_no_keyword)
             , "embedded_types_cases_no_keyword" ~: $test67_embedded_types_cases_no_keyword @=? $(dsSplice test67_embedded_types_cases_no_keyword)
             , "invis_type_pat_lambda" ~: $test68_invis_type_pat_lambda @=? $(dsSplice test68_invis_type_pat_lambda)
             , "invis_type_pat_cases" ~: $test69_invis_type_pat_cases @=? $(dsSplice test69_invis_type_pat_cases)
#endif
             ]

test35a = $test35_expand
test35b = $(test35_expand >>= dsExp >>= expand >>= return . expToTH)
test36a = $test36_expand
test36b = $(test36_expand >>= dsExp >>= expand >>= return . expToTH)
test_e3a = $test_expand3
test_e3b = $(test_expand3 >>= dsExp >>= expand >>= return . expToTH)
test_e4a = $test_expand4
test_e4b = $(test_expand4 >>= dsExp >>= expand >>= return . expToTH)
test_e5a = $test_expand5
test_e5b = $(test_expand5 >>= dsExp >>= expand >>= return . expToTH)
test_e6a = $test_expand6
test_e6b = $(test_expand6 >>= dsExp >>= expand >>= return . expToTH)
test_e7a = $test_expand7
test_e7b = $(test_expand7 >>= dsExp >>= expand >>= return . expToTH)
test_e7c = $(test_expand7 >>= dsExp >>= expandUnsoundly >>= return . expToTH)
#if __GLASGOW_HASKELL__ < 801
test_e8a = $(test_expand8 >>= dsExp >>= expand >>= return . expToTH)
  -- This won't expand on recent GHCs now that GHC Trac #8953 is fixed for
  -- closed type families.
#endif
test_e8b = $(test_expand8 >>= dsExp >>= expandUnsoundly >>= return . expToTH)
test_e9a = $test_expand9  -- requires GHC #9262
test_e9b = $(test_expand9 >>= dsExp >>= expand >>= return . expToTH)
test_e10a = $test_expand10
test_e10b = $(test_expand10 >>= dsExp >>= expand >>= return . expToTH)

hasSameType :: a -> a -> Bool
hasSameType _ _ = True

test_expand :: Bool
test_expand = and [ hasSameType test35a test35b
                  , hasSameType test36a test36b
                  , hasSameType test_e3a test_e3b
                  , hasSameType test_e4a test_e4b
                  , hasSameType test_e5a test_e5b
                  , hasSameType test_e6a test_e6b
                  , hasSameType test_e7a test_e7b
                  , hasSameType test_e7a test_e7c
#if __GLASGOW_HASKELL__ < 801
                  , hasSameType test_e8a test_e8a
#endif
                  , hasSameType test_e8b test_e8b
                  , hasSameType test_e9a test_e9b
                  , hasSameType test_e10a test_e10b
                  ]

test_dec :: [Bool]
test_dec = $(do bools <- mapM testDecSplice dec_test_nums
                return $ ListE bools)

$( do fuzzType <- mkTypeName "Fuzz"
      fuzzData <- mkDataName "Fuzz"
      let tySynDecs = TySynD (mkName "FuzzSyn") [] (ConT fuzzType)
          dataSynDecs = TySynD (mkName "FuzzDataSyn") [] (ConT fuzzData)
      fuzzDecs <- [d| data Fuzz = Fuzz |]
      return $ tySynDecs : dataSynDecs : fuzzDecs )

test_mkName :: Bool
test_mkName = and [ hasSameType (Proxy :: Proxy FuzzSyn) (Proxy :: Proxy Fuzz)
                  , hasSameType (Proxy :: Proxy FuzzDataSyn) (Proxy :: Proxy 'Fuzz) ]

test_bug8884 :: Bool
test_bug8884 = $(do info <- reify ''Poly
                    dinfo@(DTyConI (DOpenTypeFamilyD (DTypeFamilyHead _name _tvbs (DKindSig resK) _ann))
                                   (Just [DTySynInstD (DTySynEqn _ lhs _rhs)]))
                      <- dsInfo info
                    let isTypeKind (DConT n) = isTypeKindName n
                        isTypeKind _         = False
                    case (isTypeKind resK, lhs) of
                      (True, _ `DAppT` DSigT (DVarT _) (DVarT _)) -> [| True |]
                      _                                     -> do
                        runIO $ do
                          putStrLn "Failed bug8884 test:"
                          putStrLn $ show dinfo
                        [| False |] )

flatten_dvald :: Bool
flatten_dvald = let s1 = $(flatten_dvald_test)
                    s2 = $(do expr <- flatten_dvald_test
                              DLetE ddecs dexpr <- dsExp expr
                              flattened <- fmap concat $ mapM flattenDValD ddecs
                              return $ expToTH $ DLetE flattened dexpr ) in
                s1 == s2

test_rec_sels :: Bool
test_rec_sels = and $(do bools <- mapM testRecSelTypes [1..rec_sel_test_num_sels]
                         return $ ListE bools)

test_standalone_deriving :: Bool
test_standalone_deriving = (MkBlarggie 5 'x') == (MkBlarggie 5 'x')

test_deriving_strategies :: Bool
#if __GLASGOW_HASKELL__ >= 801
test_deriving_strategies = compare (MkBlarggie 5 'x') (MkBlarggie 5 'x') == EQ
#else
test_deriving_strategies = True
#endif

test_local_tyfam_expansion :: Bool
test_local_tyfam_expansion =
  $(do fam_name <- newName "Fam"
       let orig_ty = DConT fam_name
       exp_ty <- withLocalDeclarations
                   (decsToTH [ DOpenTypeFamilyD (DTypeFamilyHead fam_name [] DNoSig Nothing)
                             , DTySynInstD (DTySynEqn Nothing
                                                      (DConT fam_name) (DConT ''Int)) ])
                   (expandType orig_ty)
       orig_ty `eqTHSplice` exp_ty)

test_stuck_tyfam_expansion :: Bool
test_stuck_tyfam_expansion =
  $(do fam_name <- newName "F"
       x        <- newName "x"
       k        <- newName "k"
       let orig_ty = DConT fam_name `DAppT` DConT '() -- F '()
       exp_ty <- withLocalDeclarations
                   (decsToTH [ -- type family F (x :: k) :: k
                               DOpenTypeFamilyD
                                 (DTypeFamilyHead fam_name
                                                  [DKindedTV x THAbs.BndrReq (DVarT k)]
                                                  (DKindSig (DVarT k))
                                                  Nothing)
                               -- type instance F (x :: ()) = x
                             , DTySynInstD
                                 (DTySynEqn Nothing
                                            (DConT fam_name `DAppT`
                                               DSigT (DVarT x) (DConT ''()))
                                            (DVarT x))
                             ])
                   (expandType orig_ty)
       orig_ty `eqTHSplice` exp_ty)

test_t85 :: Bool
test_t85 =
  $(do let orig_ty =
             (DConT ''Constant `DAppT` DConT ''Int `DAppT` DConT 'True)
             `DSigT` (DConT ''Constant `DAppT` DConT ''Char `DAppT` DConT ''Bool)
           expected_ty = DConT 'True `DSigT` DConT ''Bool
       expanded_ty <- expandType orig_ty
       expected_ty `eqTHSplice` expanded_ty)

test_t92 :: Bool
test_t92 =
  $(do a <- newName "a"
       f <- newName "f"
       let t = DForallT (DForallInvis [DPlainTV f SpecifiedSpec])
                        (DVarT f `DAppT` DVarT a)
       toposortTyVarsOf [t] `eqTHSplice` [DPlainTV a ()])

test_t97 :: Bool
test_t97 =
  $(do a <- newName "a"
       k <- newName "k"
       let orig_ty = DForallT
                       (DForallInvis
                         [DKindedTV a SpecifiedSpec
                                      (DConT ''Constant `DAppT` DConT ''Int
                                                        `DAppT` DVarT k)])
                       (DVarT a)
           expected_ty = DForallT (DForallInvis
                                    [DKindedTV a SpecifiedSpec (DVarT k)])
                                  (DVarT a)
       expanded_ty <- expandType orig_ty
       expected_ty `eqTHSplice` expanded_ty)

test_getDataD_kind_sig :: Bool
test_getDataD_kind_sig =
  3 == $(do data_name <- newName "TestData"
            a         <- newName "a"
            let type_kind     = DConT typeKindName
                data_kind_sig = DArrowT `DAppT` type_kind `DAppT`
                                  (DArrowT `DAppT` type_kind `DAppT` type_kind)
            (_, tvbs, _) <-
              withLocalDeclarations
                [decToTH (DDataD Data [] data_name [DPlainTV a THAbs.BndrReq]
                                 (Just data_kind_sig) [] [])]
                (getDataD "th-desugar: Impossible" data_name)
            [| $(Syn.lift (length tvbs)) |])

test_t100 :: Bool
test_t100 =
  $(do decs <- [d| data T b where
                     MkT :: forall a. { unT :: a } -> T a |]
       info <- withLocalDeclarations decs (dsReify (mkName "unT"))
       let -- forall a. T a -> a
           exp_ty = DForallT (DForallInvis [DPlainTV (mkName "a") SpecifiedSpec]) $
                    DArrowT `DAppT` (DConT (mkName "T") `DAppT` DVarT (mkName "a"))
                            `DAppT` DVarT (mkName "a")
       case info of
         Just (DVarI _ actual_ty _) -> exp_ty `eqTHSplice` actual_ty
         _                          -> [| False |])

test_t102 :: [Bool]
test_t102 =
  $(do decs1 <- [d| data Foo x where MkFoo :: forall a. { unFoo :: a } -> Foo a |]
       let b1 = withLocalDeclarations decs1 $ do
                  [DDataD _ _ _ _ _ cons1 _] <- dsDecs decs1
                  recs1 <- getRecordSelectors cons1
                  (length recs1 `div` 2) `eqTHSplice` 1
       decs2 <- [d| data HList l where
                      Nil  :: HList '[]
                      (:>) :: { hhead :: x, htail :: HList xs } -> HList (x ': xs) |]
       let b2 = withLocalDeclarations decs2 $ do
                  [DDataD _ _ _ _ _ cons2 _] <- dsDecs decs2
                  recs2 <- getRecordSelectors cons2
                  (length recs2 `div` 2) `eqTHSplice` 2
       [| [$b1, $b2] |])

test_t103 :: Bool
test_t103 =
  $(do decs <- [d| data P (a :: k) = MkP |]
       [DDataD _ _ _ _ _ [DCon tvbs _ _ _ _] _] <- dsDecs decs
       case tvbs of
         [DPlainTV k SpecifiedSpec, DKindedTV a SpecifiedSpec (DVarT k')]
           |  nameBase k == "k"
           ,  nameBase a == "a"
           ,  k == k'
           -> [| True |]
           |  otherwise
           -> [| False |])

test_t112 :: [Bool]
test_t112 =
  $(do a <- newName "a"
       b <- newName "b"
       let aVar = DVarT a
           bVar = DVarT b
           aTvb = DPlainTV a ()
           bTvb = DPlainTV b ()

           fvsABExpected = [aTvb, bTvb]
           fvsABActual   = toposortTyVarsOf [aVar, bVar]

           fvsBAExpected = [bTvb, aTvb]
           fvsBAActual   = toposortTyVarsOf [bVar, aVar]

           eqAB = fvsABExpected `eqTH` fvsABActual
           eqBA = fvsBAExpected `eqTH` fvsBAActual
       [| [eqAB, eqBA] |])

test_t132 :: Bool
test_t132 =
  $(do let c      = mkName "C"
           m      = mkName "m"
           a      = mkName "a"
           fixity = Fixity 5 InfixR
           -- Defines a class with a fixity declaration inside, i.e.,
           --
           --   class C a where
           --     infixr 5 `m`
           --     m :: a
           --
           -- We define this by hand to avoid GHC#17608 on pre-9.0 GHCs.
           decs = sweeten [ DClassD [] c [DPlainTV a THAbs.BndrReq] []
                            [ DLetDec (DInfixD fixity NoNamespaceSpecifier m)
                            , DLetDec (DSigD m (DVarT a))
                            ]
                          ]
           expected = Just fixity
       actual <- withLocalDeclarations decs (reifyFixityWithLocals m)
       expected `eqTHSplice` actual)

#if __GLASGOW_HASKELL__ >= 801
-- Test local reification of pattern synonym record selectors.
test_t137 :: [Bool]
test_t137 =
  $(do a <- newName "a"
       b <- newName "b"
       let aVarT = DVarT a
           aVarP = DVarP a
           bVarT = DVarT b
           bVarP = DVarP b
           aTvb = DPlainTV a SpecifiedSpec
           bTvb = DPlainTV b SpecifiedSpec

           p1    = mkName "P1"
           unP1a = mkName "unP1a"
           unP1b = mkName "unP1b"
           p2    = mkName "P2"
           unP2a = mkName "unP2a"
           unP2b = mkName "unP2b"
           p3    = mkName "P3"
           unP3a = mkName "unP3a"
           unP3b = mkName "unP3b"

           tupleTy = DConT (tupleTypeName 2) `DAppT` aVarT `DAppT` bVarT
           showCxt = [DConT ''Show `DAppT` aVarT]
           patSynSigDBodyTy =
             DArrowT `DAppT` aVarT `DAppT` (DArrowT `DAppT` bVarT `DAppT` tupleTy)

           -- pattern P{unPa, unPb} = (unPa, unPb)
           mkPatSynD :: Name -> Name -> Name -> DDec
           mkPatSynD p unPa unPb =
             DPatSynD
               p
               (RecordPatSyn [unPa, unPb])
               DImplBidir
               (DConP (tupleDataName 2) [] [aVarP, bVarP])

           decs :: [Dec]
           decs = sweeten
             [ -- pattern P1 :: a -> b -> (a, b)
               DPatSynSigD p1 patSynSigDBodyTy
             , mkPatSynD p1 unP1a unP1b

               -- pattern P2 :: Show a => a -> b -> (a, b)
             , DPatSynSigD p2 $ DConstrainedT showCxt patSynSigDBodyTy
             , mkPatSynD p2 unP2a unP2b

               -- pattern P3 :: forall b a. Show a => a -> b -> (a, b)
             , DPatSynSigD p3 $
                 DForallT (DForallInvis [bTvb, aTvb]) $
                 DConstrainedT showCxt patSynSigDBodyTy
             , mkPatSynD p3 unP3a unP3b
             ]

           -- Pair each pattern synonym record selector name with the type that
           -- local reification should produce.
           expecteds :: [(Name, DType)]
           expecteds =
             [ (unP1a, DForallT (DForallInvis [aTvb, bTvb]) $
                       DArrowT `DAppT` tupleTy `DAppT` aVarT)
             , (unP1b, DForallT (DForallInvis [aTvb, bTvb]) $
                       DArrowT `DAppT` tupleTy `DAppT` bVarT)

               -- The reified types below use (DForallInvis []) due to the way
               -- that ForallT is desugared.
               -- See Note [Desugaring and sweetening ForallT] in
               -- Language.Haskell.TH.Desugar.Core.
             , (unP2a, DForallT (DForallInvis []) $
                       DConstrainedT showCxt $
                       DArrowT `DAppT` tupleTy `DAppT` aVarT)
             , (unP2b, DForallT (DForallInvis []) $
                       DConstrainedT showCxt $
                       DArrowT `DAppT` tupleTy `DAppT` bVarT)

             , (unP3a, DForallT (DForallInvis [bTvb, aTvb]) $
                       DConstrainedT showCxt $
                       DArrowT `DAppT` tupleTy `DAppT` aVarT)
             , (unP3b, DForallT (DForallInvis [bTvb, aTvb]) $
                       DConstrainedT showCxt $
                       DArrowT `DAppT` tupleTy `DAppT` bVarT)
             ]

           expected_eq_actual :: (Name, DType) -> DsM Q Bool
           expected_eq_actual (sel_name, expected_ty) = do
              let expected_info = Just $ DVarI sel_name expected_ty Nothing
              actual_info <- dsReify sel_name
              pure $ expected_info `eqTH` actual_info

       bs <- withLocalDeclarations decs $ mapM expected_eq_actual expecteds
       Syn.lift bs)
#endif

test_t154 :: Bool
test_t154 =
  $(do decs  <- [d| data T where
                     (:$$:) :: Int -> Int -> T
                  |]
       ddecs <- dsDecs decs
       let mb_is_infix = case ddecs of
                           [DDataD _ _ _ _ _ [DCon _ _ _ (DNormalC is_infix _) _] _]
                             -> Just is_infix
                           _ -> Nothing
       mb_is_infix `eqTHSplice` Just False)

-- Regression test for #159 which ensures that non-exhaustive functions throw
-- a runtime error before forcing their arguments.
test_t159 :: Expectation
test_t159 = do
  -- NB: Catch ErrorCall here, not PatternMatchFail. This is because we desugar
  -- non-exhaustive patterns into a custom `error` expression.
  let testOne f = f (let x = x in x) `shouldThrow` \(_ :: ErrorCall) -> True
  testOne t159A
  testOne t159B

#if __GLASGOW_HASKELL__ >= 906
test_t170 :: [Bool]
test_t170 =
  $(do decs <- [d| type data TyData = MkTyData |]

       let test_TypeData_NameSpace nameStr =
             withLocalDeclarations decs $ do
               Just name <- lookupTypeNameWithLocals nameStr
               mbNS <- reifyNameSpace name
               mbNS `eqTHSplice` Just Syn.TcClsName

       let b1 = test_TypeData_NameSpace "TyData"
       let b2 = test_TypeData_NameSpace "MkTyData"
       [| [$b1, $b2] |])
#endif

test_t171 :: Bool
test_t171 =
  $(do a <- newName "a"
       b <- newName "b"
       c <- newName "c"
       x <- newName "x"
       y <- newName "y"

       let aVarT = DVarT a
           bVarT = DVarT b
           cVarT = DVarT c
           aTvb  = DPlainTV a SpecifiedSpec
           bTvb  = DPlainTV b SpecifiedSpec
           cTvb  = DPlainTV c SpecifiedSpec
           t     = mkName "T"
           mkT   = mkName "mkT"
           getT1 = mkName "getT1"
           getT2 = mkName "getT2"

           dec = -- data T x y where
                 --   MkT :: forall b a c. { getT1 :: b, getT2 :: c } -> T a b
                 DDataD
                   Data
                   []
                   t
                   [DPlainTV x THAbs.BndrReq, DPlainTV y THAbs.BndrReq]
                   Nothing
                   [ DCon
                       [bTvb, aTvb, cTvb]
                       []
                       mkT
                       (DRecC [ ( getT1
                                , Bang NoSourceUnpackedness NoSourceStrictness
                                , bVarT
                                )
                              , ( getT2
                                , Bang NoSourceUnpackedness NoSourceStrictness
                                , cVarT
                                )
                              ])
                       res_ty
                   ]
                   []
           res_ty = DConT t `DAppT` aVarT `DAppT` bVarT
           expected_ty = DForallT (DForallInvis [bTvb, aTvb]) $
                         DArrowT `DAppT` res_ty `DAppT` bVarT

       withLocalDeclarations (sweeten [dec]) $ do
         Just (DVarI _ actual_ty _) <- dsReify getT1
         expected_ty `eqTHSplice` actual_ty)

-- Unit tests for tupleNameDegree_maybe. These also act as a regression test for
-- #187.
test_t187 :: [Bool]
test_t187 =
  map (\(s, expected) -> tupleNameDegree_maybe s == expected)
    [ (''(),                Just 0)
    , (''(,),               Just 2)
    , (''(,,),              Just 3)
    , (''Maybe,             Nothing)
    , (tupleTypeName 0,     Just 0)
    , (tupleTypeName 2,     Just 2)
    , (tupleTypeName 3,     Just 3)
#if __GLASGOW_HASKELL__ >= 900
    , (''Solo,              Just 1)
#if __GLASGOW_HASKELL__ >= 906
    , ('MkSolo,             Just 1)
#else
    , ('Solo,               Just 1)
#endif
#endif
#if __GLASGOW_HASKELL__ >= 908
    , (''Unit,              Just 0)
    , (''Tuple0,            Just 0)
    , (''Tuple1,            Just 1)
    , (''Tuple2,            Just 2)
    , (''Tuple3,            Just 3)
    , (''FakeTuples.Tuple0, Nothing)
    , (''FakeTuples.Tuple1, Nothing)
    , (''FakeTuples.Tuple2, Nothing)
    , (''FakeTuples.Tuple3, Nothing)
#endif
    ]

-- A regression test for #188, which ensures that it produces the correct answer
-- for an unusual telescope like:
--
--   ... forall (a1 :: a2). forall (a2 :: a1). ...
--
-- Here, a2 is free in the kind of a1 (the first `forall`), but then the second
-- `forall` binds another a2 that shadows what was already in scope. In this
-- example, `toposortKindVarsOfTvbs [(a1 :: a2), (a2 :: a1)]` should return
-- [a2].
test_t188 :: Bool
test_t188 =
  let a1 = mkName "a1"
      a2 = mkName "a2" in
  toposortKindVarsOfTvbs [DKindedTV a1 () (DVarT a2), DKindedTV a2 () (DVarT a1)]
    == [DPlainTV a2 ()]

-- Unit tests for unboxedTupleNameDegree_maybe and unboxedSumNameDegree_maybe.
-- These also act as a regression test for #213.
test_t213 :: [Bool]
test_t213 =
  map (\(s, expected) -> unboxedTupleNameDegree_maybe s == expected)
    [ (''(##),                 Just 0)
    , (''(#,#),                Just 2)
    , (''(#,,#),               Just 3)
    , (''Maybe,                Nothing)
#if __GLASGOW_HASKELL__ >= 802
    , (unboxedTupleTypeName 0, Just 0)
#endif
    , (unboxedTupleTypeName 2, Just 2)
    , (unboxedTupleTypeName 3, Just 3)
#if __GLASGOW_HASKELL__ >= 910
    , (''Unit#,                Just 0)
    , (''Tuple0#,              Just 0)
    , (''Solo#,                Just 1)
    , (''Tuple1#,              Just 1)
    , (''Tuple2#,              Just 2)
    , (''Tuple3#,              Just 3)
    , (''FakeTuples.Tuple0#,   Nothing)
    , (''FakeTuples.Tuple1#,   Nothing)
    , (''FakeTuples.Tuple2#,   Nothing)
    , (''FakeTuples.Tuple3#,   Nothing)
#endif
    ]
#if __GLASGOW_HASKELL__ >= 802
  ++
  map (\(s, expected) -> unboxedSumNameDegree_maybe s == expected)
    [ (unboxedSumTypeName 2, Just 2)
    , (unboxedSumTypeName 3, Just 3)
    , (unboxedSumTypeName 4, Just 4)
#if __GLASGOW_HASKELL__ >= 910
    , (''Sum2#,              Just 2)
    , (''Sum3#,              Just 3)
    , (''Sum4#,              Just 4)
    , (''FakeSums.Sum2#,     Nothing)
    , (''FakeSums.Sum3#,     Nothing)
    , (''FakeSums.Sum4#,     Nothing)
#endif
    ]
#endif

-- Unit tests for functions that compute free variables (e.g., fvDType)
test_fvs :: [Bool]
test_fvs =
  $(do a <- newName "a"

       let -- (Show a => Show (Maybe a)) => String
           ty1 = DConstrainedT
                   [DConstrainedT [DConT ''Show `DAppT` DVarT a]
                                  (DConT ''Show `DAppT` (DConT ''Maybe `DAppT` DVarT a))]
                   (DConT ''String)
           b1 = fvDType ty1 `eqTH` OS.singleton a -- #93

       [| [b1] |])

test_kind_substitution :: [Bool]
test_kind_substitution =
  $(do a <- newName "a"
       b <- newName "b"
       c <- newName "c"
       k <- newName "k"
       let subst = M.singleton a (DVarT b)

                 -- (Nothing :: Maybe a)
           ty1 = DSigT (DConT 'Nothing) (DConT ''Maybe `DAppT` DVarT a)
                 -- forall (c :: a). c
           ty2 = DForallT (DForallInvis [DKindedTV c SpecifiedSpec (DVarT a)])
                          (DVarT c)
                 -- forall a (c :: a). c
           ty3 = DForallT (DForallInvis [ DPlainTV  a SpecifiedSpec
                                        , DKindedTV c SpecifiedSpec (DVarT a)
                                        ])
                          (DVarT c)
                 -- forall (a :: k) k (b :: k). Proxy b -> Proxy a
           ty4 = DForallT (DForallInvis
                             [ DKindedTV a SpecifiedSpec (DVarT k)
                             , DPlainTV  k SpecifiedSpec
                             , DKindedTV b SpecifiedSpec (DVarT k)
                             ])
                          (DArrowT `DAppT` (DConT ''Proxy `DAppT` DVarT b)
                                   `DAppT` (DConT ''Proxy `DAppT` DVarT a))

       substTy1 <- substTy subst ty1
       substTy2 <- substTy subst ty2
       substTy3 <- substTy subst ty3
       substTy4 <- substTy subst ty4

       let freeVars1 = fvDType substTy1
           freeVars2 = fvDType substTy2
           freeVars3 = fvDType substTy3
           freeVars4 = fvDType substTy4

           b1 = freeVars1 `eqTH` OS.singleton b
           b2 = freeVars2 `eqTH` OS.singleton b
           b3 = freeVars3 `eqTH` OS.empty
           b4 = freeVars4 `eqTH` OS.singleton k
       [| [b1, b2, b3, b4] |])

test_lookup_value_type_names :: [Bool]
test_lookup_value_type_names =
  $(do let nameStr = "***"
       valName  <- newName nameStr
       typeName <- newName nameStr
       let tyDec = DTySynD typeName [] (DConT ''Bool)
           decs  = decsToTH [ DLetDec (DSigD valName (DConT ''Bool))
                            , DLetDec (DValD (DVarP valName) (DConE 'False))
                            , tyDec ]
           lookupReify lookup_fun = withLocalDeclarations decs $ do
                                      Just n <- lookup_fun nameStr
                                      Just i <- dsReify n
                                      return i
       reifiedVal  <- lookupReify lookupValueNameWithLocals
       reifiedType <- lookupReify lookupTypeNameWithLocals
       let b1 = reifiedVal  `eqTH` DVarI valName (DConT ''Bool) Nothing
       let b2 = reifiedType `eqTH` DTyConI tyDec Nothing
       [| [b1, b2] |])

local_reifications :: [String]
local_reifications = $(do decs <- reifyDecs
                          m_infos <- withLocalDeclarations decs $
                                     mapM reifyWithLocals_maybe reifyDecsNames
                          let m_infos' = assumeStarT m_infos
                          ListE <$> mapM (Syn.lift . show) (unqualify m_infos'))

type T123G = Either () ()
type T123F = Either T123G T123G
type T123E = Either T123F T123F
type T123D = Either T123E T123E
type T123C = Either T123D T123D
type T123B = Either T123C T123C
type T123A = Either T123B T123B

$reifyDecs

$(return [])  -- somehow, this is necessary to get the staging correct for the
              -- reifications below. Weird.

normal_reifications :: [String]
normal_reifications = $(do infos <- mapM reify reifyDecsNames
                           ListE <$> mapM (Syn.lift . show . Just)
                                          (dropTrailing0s $ delinearize $ unqualify infos))

zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f (a:as) (b:bs) (c:cs) = liftM2 (:) (f a b c) (zipWith3M f as bs cs)
zipWith3M _ _ _ _ = return []

simplCase :: [Bool]
simplCase = $( do exps <- sequence simplCaseTests
                  dexps <- mapM dsExp exps
                  sexps <- mapM scExp dexps
                  bools <- zipWithM (\e1 e2 -> [| $(return e1) == $(return e2) |])
                    exps (map sweeten sexps)
                  return $ ListE bools )

test_roundtrip :: [Bool]
test_roundtrip = $( do exprs <- sequence test_exprs
                       ds_exprs1 <- mapM dsExp exprs
                       let th_exprs1 = map expToTH ds_exprs1
                       ds_exprs2 <- mapM dsExp th_exprs1
                       let th_exprs2 = map expToTH ds_exprs2
                       ds_exprs3 <- mapM dsExp th_exprs2
                       let bools = zipWith eqTH ds_exprs2 ds_exprs3
                       Syn.lift bools )

test_matchTy :: [Bool]
test_matchTy =
  [ matchTy NoIgnore (DVarT a) (DConT ''Bool) == Just (M.singleton a (DConT ''Bool))
  , matchTy NoIgnore (DVarT a) (DVarT a) == Just (M.singleton a (DVarT a))
  , matchTy NoIgnore (DVarT a) (DVarT b) == Just (M.singleton a (DVarT b))
  , matchTy NoIgnore (DConT ''Either `DAppT` DVarT a `DAppT` DVarT b)
                     (DConT ''Either `DAppT` DConT ''Int `DAppT` DConT ''Bool)
    == Just (M.fromList [(a, DConT ''Int), (b, DConT ''Bool)])
  , matchTy NoIgnore (DConT ''Either `DAppT` DVarT a `DAppT` DVarT a)
                     (DConT ''Either `DAppT` DConT ''Int `DAppT` DConT ''Int)
    == Just (M.singleton a (DConT ''Int))
  , matchTy NoIgnore (DConT ''Either `DAppT` DVarT a `DAppT` DVarT a)
                     (DConT ''Either `DAppT` DConT ''Int `DAppT` DConT ''Bool)
    == Nothing
  , matchTy NoIgnore (DConT ''Int) (DConT ''Bool) == Nothing
  , matchTy NoIgnore (DConT ''Int) (DConT ''Int) == Just M.empty
  , matchTy NoIgnore (DConT ''Int) (DVarT a) == Nothing
    -- Test `DSigT` with both `IgnoreKinds` options
  , matchTy NoIgnore (DVarT a `DSigT` DConT ''Bool) (DConT ''Int) == Nothing
  , matchTy YesIgnore (DVarT a `DSigT` DConT ''Bool) (DConT ''Int)
    == Just (M.singleton a (DConT ''Int))
    -- Test `DAppKindT` with both `IgnoreKinds` options
  , matchTy NoIgnore (DConT ''Proxy `DAppKindT` DConT ''Bool `DAppT` DVarT a)
                     (DConT ''Proxy `DAppT` DConT ''Int)
    == Nothing
  , matchTy YesIgnore (DConT ''Proxy `DAppKindT` DConT ''Bool `DAppT` DVarT a)
                      (DConT ''Proxy `DAppT` DConT ''Int)
    == Just (M.singleton a (DConT ''Int))
  ]
  where
    a = mkName "a"
    b = mkName "b"

-- Test that type synonym expansion is efficient
test_t123 :: ()
test_t123 =
  $(do _ <- expand (DConT ''T123A)
       [| () |])

main :: IO ()
main = hspec $ do
  describe "th-desugar library" $ do
    it "compiles" $ True
    it "expands"  $ test_expand

    zipWithM (\num success -> it ("passes dec test " ++ show num) success)
      dec_test_nums test_dec

    -- instance test 1 is part of dectest 6.
    it "passes instance test" $ $(do ty <- [t| Int -> Bool |]
                                     [inst1, inst2] <- reifyInstances ''Show [ty]
                                     inst1 `eqTHSplice` inst2)

    it "makes type names" $ test_mkName

    it "fixes bug 8884" $ test_bug8884

    it "flattens DValDs" $ flatten_dvald

    it "extracts record selectors" $ test_rec_sels

    it "works with standalone deriving" $ test_standalone_deriving

    it "works with deriving strategies" $ test_deriving_strategies

    it "doesn't expand local type families" $ test_local_tyfam_expansion

    it "doesn't crash on a stuck type family application" $ test_stuck_tyfam_expansion

    it "expands type synonyms in kinds" $ test_t85

    it "toposorts free variables in polytypes" $ test_t92

    it "expands type synonyms in type variable binders" $ test_t97

    it "reifies GADT record selectors correctly" $ test_t100

    zipWithM (\b n -> it ("collects GADT record selectors correctly" ++ show n) b)
      test_t102 [1..]

    it "quantifies kind variables in desugared ADT constructors" $ test_t103

    it "reifies data type return kinds accurately" $ test_getDataD_kind_sig

    zipWithM (\b n -> it ("toposorts free variables deterministically " ++ show n) b)
      test_t112 [1..]

    it "reifies fixity declarations inside of classes" $ test_t132

#if __GLASGOW_HASKELL__ >= 801
    zipWithM (\b n -> it ("reifies local pattern synonym record selectors " ++ show n) b)
      test_t137 [1..]
#endif

    zipWithM (\b n -> it ("computes free variables correctly " ++ show n) b)
      test_fvs [1..]

    it "desugars non-infix GADT constructors with symbolic names correctly" $ test_t154

    it "desugars non-exhaustive expressions into code that errors at runtime" $ test_t159

#if __GLASGOW_HASKELL__ >= 906
    zipWithM (\b n -> it ("looks up TypeData names in the type namespace correctly " ++ show n) b)
      test_t170 [1..]
#endif

    it "locally reifies GADT record selector types with explicit foralls correctly" $ test_t171

    it "doesn't reify a field selector with lookupValueNameWithLocals when NoFieldSelectors is set" $
      t183 == Nothing

    zipWithM (\b n -> it ("recognizes tuple names with tupleDegree_maybe correctly " ++ show n) b)
      test_t187 [1..]

    it "computes free kind variables correctly in a telescope that uses shadowing" $ test_t188

    zipWithM (\b n -> it ("recognizes unboxed {tuple,sum} names with unboxed{Tuple,Sum}Degree_maybe correctly " ++ show n) b)
      test_t213 [1..]

    -- Remove map pprints here after switch to th-orphans
    zipWithM (\t t' -> it ("can do Type->DType->Type of " ++ t) $ t == t')
             $(sequence round_trip_types >>= Syn.lift . map pprint)
             $(sequence round_trip_types >>=
               mapM (\ t -> withLocalDeclarations [] (dsType t >>= expandType >>= return . typeToTH)) >>=
              Syn.lift . map pprint)

    zipWith3M (\a b nm -> it ("reifies local definition " ++ nameBase nm) $ a == b)
      local_reifications normal_reifications reifyDecsNames

    zipWithM (\b n -> it ("works on simplCase test " ++ show n) b) simplCase [1..]

    zipWithM (\b n -> it ("round-trip successfully on case " ++ show n) b) test_roundtrip [1..]

    zipWithM (\b n -> it ("lookups up local value and type names " ++ show n) b)
      test_lookup_value_type_names [1..]

    zipWithM (\b n -> it ("substitutes tyvar binder kinds " ++ show n) b)
      test_kind_substitution [1..]

    zipWithM (\b n -> it ("matches types " ++ show n) b)
      test_matchTy [1..]

    zipWithM (\b n -> it ("reifies kinds of declarations with CUSKs " ++ show n) b)
      test_reify_type_cusks [1..]

    zipWithM (\b n -> it ("reifies kinds of declarations without CUSKs " ++ show n) b)
      test_reify_type_no_cusks [1..]

    zipWithM (\b n -> it ("reifies the kinds of declarations with signatures " ++ show n) b)
      test_reify_kind_sigs [1..]

    fromHUnitTest tests
