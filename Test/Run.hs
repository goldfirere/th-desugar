{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, UnboxedTuples, ParallelListComp, CPP,
             RankNTypes, ImpredicativeTypes, TypeFamilies,
             DataKinds, ConstraintKinds #-}
{-# OPTIONS -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns
            -fno-warn-unused-matches -fno-warn-type-defaults
            -fno-warn-missing-signatures -fno-warn-unused-do-bind #-}

module Test.Run where

import Test.HUnit
import Test.Hspec
import Test.Hspec.HUnit

import Test.Splices
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Expand
import Language.Haskell.TH.Desugar.Sweeten

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
-- type signatures in patterns not yet handled by Template Haskell
--           , "sigp"     ~: $test23_sigp     @=? $(dsSplice test23_sigp)
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
             ]

test35a = $test35_expand
test35b = $(test35_expand >>= dsExp >>= expand >>= return . expToTH)
test36a = $test36_expand
test36b = $(test36_expand >>= dsExp >>= expand >>= return . expToTH)

hasSameType :: a -> a -> Bool
hasSameType _ _ = True

test_expand :: Bool
test_expand = and [ hasSameType test35a test35b
                  , hasSameType test36a test36b]

main :: IO ()
main = hspec $ do
  describe "th-desugar library" $ do
    it "compiles" $ True
    it "expands"  $ test_expand

    fromHUnitTest tests