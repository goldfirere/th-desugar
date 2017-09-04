{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE TemplateHaskell, UnboxedTuples, ParallelListComp, CPP,
             RankNTypes, ImpredicativeTypes, TypeFamilies,
             DataKinds, ConstraintKinds, PolyKinds, MultiParamTypeClasses,
             FlexibleInstances, ExistentialQuantification,
             ScopedTypeVariables, GADTs, ViewPatterns #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns
            -fno-warn-unused-matches -fno-warn-type-defaults
            -fno-warn-missing-signatures -fno-warn-unused-do-bind #-}

#if __GLASGOW_HASKELL__ >= 711
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures -Wno-redundant-constraints #-}
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
import Language.Haskell.TH.Desugar
#if __GLASGOW_HASKELL__ >= 707
import Language.Haskell.TH.Desugar.Expand  ( expandUnsoundly )
#endif
import Language.Haskell.TH
import qualified Language.Haskell.TH.Syntax as Syn ( lift )

import Control.Monad
#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif

import qualified Data.Map as M
import qualified Data.Set as S
#if __GLASGOW_HASKELL__ >= 707
import Data.Proxy
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
#if __GLASGOW_HASKELL__ >= 707
             , "parcomp"  ~: $test11_parcomp  @=? $(dsSplice test11_parcomp)
             , "parcomp2" ~: $test12_parcomp2 @=? $(dsSplice test12_parcomp2)
#endif
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
#if __GLASGOW_HASKELL__ >= 709
             , "pred"     ~: $test37_pred     @=? $(dsSplice test37_pred)
             , "pred2"    ~: $test38_pred2    @=? $(dsSplice test38_pred2)
             , "eq"       ~: $test39_eq       @=? $(dsSplice test39_eq)
#endif
#if __GLASGOW_HASKELL__ >= 711
             , "wildcard" ~: $test40_wildcards@=? $(dsSplice test40_wildcards)
#endif
#if __GLASGOW_HASKELL__ >= 801
             , "typeapps"   ~: $test41_typeapps   @=? $(dsSplice test41_typeapps)
             , "scoped_tvs" ~: $test42_scoped_tvs @=? $(dsSplice test42_scoped_tvs)
             , "ubx_sums"   ~: $test43_ubx_sums   @=? $(dsSplice test43_ubx_sums)
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
#if __GLASGOW_HASKELL__ >= 707
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
#endif
#if __GLASGOW_HASKELL__ >= 709
test_e9a = $test_expand9  -- requires GHC #9262
test_e9b = $(test_expand9 >>= dsExp >>= expand >>= return . expToTH)
#endif

hasSameType :: a -> a -> Bool
hasSameType _ _ = True

test_expand :: Bool
test_expand = and [ hasSameType test35a test35b
                  , hasSameType test36a test36b
                  , hasSameType test_e3a test_e3b
                  , hasSameType test_e4a test_e4b
#if __GLASGOW_HASKELL__ >= 707
                  , hasSameType test_e5a test_e5b
                  , hasSameType test_e6a test_e6b
                  , hasSameType test_e7a test_e7b
                  , hasSameType test_e7a test_e7c
#if __GLASGOW_HASKELL__ < 801
                  , hasSameType test_e8a test_e8a
#endif
                  , hasSameType test_e8b test_e8b
#endif
#if __GLASGOW_HASKELL__ >= 709
                  , hasSameType test_e9a test_e9b
#endif
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
                                   (Just [DTySynInstD _name2 (DTySynEqn lhs _rhs)]))
                      <- dsInfo info
                    case (resK, lhs) of
#if __GLASGOW_HASKELL__ < 709
                      (DStarT, [DVarT _]) -> [| True |]
#else
                      (DStarT, [DSigT (DVarT _) (DVarT _)]) -> [| True |]
#endif
                      _                                     -> do
                        runIO $ do
                          putStrLn "Failed bug8884 test:"
                          putStrLn $ show dinfo
                        [| False |] )

flatten_dvald :: Bool
flatten_dvald = let s1 = $(flatten_dvald_test)
                    s2 = $(do exp <- flatten_dvald_test
                              DLetE ddecs dexp <- dsExp exp
                              flattened <- fmap concat $ mapM flattenDValD ddecs
                              return $ expToTH $ DLetE flattened dexp ) in
                s1 == s2

test_rec_sels :: Bool
test_rec_sels = and $(do bools <- mapM testRecSelTypes [1..rec_sel_test_num_sels]
                         return $ ListE bools)

test_standalone_deriving :: Bool
#if __GLASGOW_HASKELL__ >= 709
test_standalone_deriving = (MkBlarggie 5 'x') == (MkBlarggie 5 'x')
#else
test_standalone_deriving = True
#endif

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
                             , DTySynInstD fam_name (DTySynEqn [] (DConT ''Int)) ])
                   (expandType orig_ty)
       orig_ty `eqTHSplice` exp_ty)

test_kind_substitution :: [Bool]
test_kind_substitution =
  $(do a <- newName "a"
       b <- newName "b"
       c <- newName "c"
       let subst = M.singleton a (DVarT b)

                 -- (Nothing :: Maybe a)
           ty1 = DSigT (DConT 'Nothing) (DConT ''Maybe `DAppT` DVarT a)
                 -- forall (c :: a). c
           ty2 = DForallT [DKindedTV c (DVarT a)] [] (DVarT c)
                 -- forall a (c :: a). c
           ty3 = DForallT [DPlainTV a, DKindedTV c (DVarT a)] [] (DVarT c)

       substTy1 <- substTy subst ty1
       substTy2 <- substTy subst ty2
       substTy3 <- substTy subst ty3

       let freeVars1 = freeVarsOfTy substTy1
           freeVars2 = freeVarsOfTy substTy2
           freeVars3 = freeVarsOfTy substTy3

           b1 = freeVars1 `eqTH` S.fromList [b]
           b2 = freeVars2 `eqTH` S.fromList [b]
           b3 = freeVars3 `eqTH` S.empty
       [| [b1, b2, b3] |])

test_lookup_value_type_names :: [Bool]
test_lookup_value_type_names =
  $(do let nameStr = "***"
       valName  <- newName nameStr
       typeName <- newName nameStr
       let tyDec = DTySynD typeName [] (DConT ''Bool)
           decs  = decsToTH [ DLetDec (DSigD valName (DConT ''Bool))
                            , DLetDec (DValD (DVarPa valName) (DConE 'False))
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

$reifyDecs

$(return [])  -- somehow, this is necessary to get the staging correct for the
              -- reifications below. Weird.

normal_reifications :: [String]
normal_reifications = $(do infos <- mapM reify reifyDecsNames
                           ListE <$> mapM (Syn.lift . show . Just)
                                          (dropTrailing0s $ unqualify infos))

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

#if __GLASGOW_HASKELL__ < 707
    it "passes roles test" $ (decsToTH [ds_role_test]) `eqTH` role_test
#endif

    it "makes type names" $ test_mkName

    it "fixes bug 8884" $ test_bug8884

    it "flattens DValDs" $ flatten_dvald

    it "extracts record selectors" $ test_rec_sels

    it "works with standalone deriving" $ test_standalone_deriving

    it "works with deriving strategies" $ test_deriving_strategies

    it "doesn't expand local type families" $ test_local_tyfam_expansion

    -- Remove map pprints here after switch to th-orphans
    zipWithM (\t t' -> it ("can do Type->DType->Type of " ++ t) $ t == t')
             $(sequence round_trip_types >>= Syn.lift . map pprint)
             $(sequence round_trip_types >>=
               mapM (\ t -> withLocalDeclarations [] (dsType t >>= expandType >>= return . typeToTH)) >>=
              Syn.lift . map pprint)

    zipWith3M (\a b n -> it ("reifies local definition " ++ show n) $ a == b)
      local_reifications normal_reifications [1..]

    zipWithM (\b n -> it ("works on simplCase test " ++ show n) b) simplCase [1..]

    zipWithM (\b n -> it ("round-trip successfully on case " ++ show n) b) test_roundtrip [1..]

    zipWithM (\b n -> it ("lookups up local value and type names " ++ show n) b)
      test_lookup_value_type_names [1..]

    zipWithM (\b n -> it ("substitutes tyvar binder kinds " ++ show n) b)
      test_kind_substitution [1..]

    fromHUnitTest tests
