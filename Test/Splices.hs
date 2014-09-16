{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, MagicHash, UnboxedTuples,
             MultiWayIf, ParallelListComp, CPP, BangPatterns,
             ScopedTypeVariables, RankNTypes, TypeFamilies, ImpredicativeTypes,
             DataKinds, PolyKinds, GADTs, MultiParamTypeClasses,
             FunctionalDependencies, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-type-defaults
                -fno-warn-name-shadowing #-}

module Test.Splices where

import Data.List
import Data.Char
import GHC.Exts
import GHC.TypeLits

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Sweeten
import Data.Generics

#if __GLASGOW_HASKELL__ < 707
data Proxy a = Proxy
#endif

dsSplice :: Q Exp -> Q Exp
dsSplice expq = expq >>= dsExp >>= (return . expToTH)

dsDecSplice :: Q [Dec] -> Q [Dec]
dsDecSplice decsQ = decsQ >>= dsDecs >>= (return . decsToTH)

testDecSplice :: Int -> Q Exp
testDecSplice n = do
  let dsName  = mkName $ "Test.DsDec.Dec" ++ show n
      regName = mkName $ "Test.Dec.Dec" ++ show n
  infoDs  <- reify dsName
  infoReg <- reify regName
#if __GLASGOW_HASKELL__ < 707
  eqTHSplice infoDs infoReg
#else
  rolesDs  <- reifyRoles dsName
  rolesReg <- reifyRoles regName
  eqTHSplice (infoDs, rolesDs) (infoReg, rolesReg)
#endif

unqualify :: Data a => a -> a
unqualify = everywhere (mkT (mkName . nameBase))

dropTrailing0s :: Data a => a -> a
dropTrailing0s = everywhere (mkT (mkName . frob . nameBase))
  where
    frob str
      | head str == 'r' = str
      | head str == 'R' = str
      | otherwise       = dropWhileEnd isDigit str

eqTH :: (Data a, Show a) => a -> a -> Bool
eqTH a b = show (unqualify a) == show (unqualify b)

eqTHSplice :: (Data a, Show a) => a -> a -> Q Exp
eqTHSplice a b =
  if a `eqTH` b
  then [| True |]
  else [| False |]


test1_sections = [| map ((* 3) . (4 +) . (\x -> x * x)) [10, 11, 12] |]
test2_lampats = [| (\(Just x) (Left z) -> x + z) (Just 5) (Left 10) |]
test3_lamcase = [| foldr (-) 0 (map (\case { Just x -> x ; Nothing -> (-3) }) [Just 1, Nothing, Just 19, Nothing]) |]
test4_tuples = [| (\(a, _) (# b, _ #) -> a + b) (1,2) (# 3, 4 #) |]
test5_ifs = [| if (5 > 7) then "foo" else if | Nothing <- Just "bar", True -> "blargh" | otherwise -> "bum" |]
test6_ifs2 = [| if | Nothing <- Nothing, False -> 3 | Just _ <- Just "foo" -> 5 |]
test7_let = [| let { x :: Double; x = 5; f :: Double -> Double; f x = x + 1 } in f (x * 2) + x |]
test8_case = [| case Just False of { Just True -> 1 ; Just _ -> 2 ; Nothing -> 3 } |]
test9_do = [| show $ do { foo <- Just "foo"
                        ; let fool = foo ++ "l"
                        ; elemIndex 'o' fool
                        ; x <- elemIndex 'l' fool
                        ; return (x + 10) } |]
test10_comp = [| [ (x, x+1) | x <- [1..10], x `mod` 2 == 0 ] |]
#if __GLASGOW_HASKELL__ >= 707
test11_parcomp = [| [ (x,y) | x <- [1..10], x `mod` 2 == 0 | y <- [2,5..20] ] |]
test12_parcomp2 = [| [ (x,y,z) | x <- [1..10], z <- [3..100], x + z `mod` 2 == 0 | y <- [2,5..20] ] |]
#endif
test13_sig = [| show (read "[10, 11, 12]" :: [Int]) |]

data Record = MkRecord1 { field1 :: Bool, field2 :: Int }
            | MkRecord2 { field2 :: Int, field3 :: Char }

test14_record = [| let r1 = [MkRecord1 { field2 = 5, field1 = False }, MkRecord2 { field2 = 6, field3 = 'q' }]
                       r2 = map (\r -> r { field2 = 18 }) r1
                       r3 = (head r2) { field1 = True } in
                   map (\case MkRecord1 { field2 = some_int, field1 = some_bool } -> show some_int ++ show some_bool
                              MkRecord2 { field2 = some_int, field3 = some_char } -> show some_int ++ show some_char) (r3 : r2) |]

test15_litp = [| map (\case { 5 -> True ; _ -> False }) [5,6] |]
test16_tupp = [| map (\(x,y,z) -> x + y + z) [(1,2,3),(4,5,6)] |]

data InfixType = Int :+: Bool
  deriving (Show, Eq)

test17_infixp = [| map (\(x :+: y) -> if y then x + 1 else x - 1) [5 :+: True, 10 :+: False] |]
test18_tildep = [| map (\ ~() -> Nothing :: Maybe Int) [undefined, ()] |]
test19_bangp = [| map (\ !() -> 5) [()] |]
test20_asp = [| map (\ a@(b :+: c) -> (if c then b + 1 else b - 1, a)) [5 :+: True, 10 :+: False] |]
test21_wildp = [| zipWith (\_ _ -> 10) [1,2,3] ['a','b','c'] |]
test22_listp = [| map (\ [a,b,c] -> a + b + c) [[1,2,3],[4,5,6]] |]
-- type signatures in patterns not yet handled by Template Haskell
-- test23_sigp = [| map (\ (a :: Int) -> a + a) [5, 10] |]

test24_fun = [| let f (Just x) = x
                    f Nothing = Nothing in
                f (Just (Just 10)) |]

test25_fun2 = [| let f (Just x)
                       | x > 0 = x
                       | x < 0 = x + 10
                     f Nothing = 0
                     f _ = 18 in
                 map f [Just (-5), Just 5, Just 10, Nothing, Just 0] |]

test26_forall = [| let f :: Num a => a -> a
                       f x = x + 10 in
                   (f 5, f 3.0) |]

test27_kisig = [| let f :: Proxy (a :: Bool) -> ()
                      f _ = () in
                  (f (Proxy :: Proxy False), f (Proxy :: Proxy True)) |]
test28_tupt = [| let f :: (a,b) -> a
                     f (a,_) = a in
                 map f [(1,'a'),(2,'b')] |]
test29_listt = [| let f :: [[a]] -> a
                      f = head . head in
                  map f [ [[1]], [[2]] ] |]
test30_promoted = [| let f :: Proxy '() -> Proxy '[Int, Bool] -> ()
                         f _ _ = () in
                     f Proxy Proxy |]
test31_constraint = [| let f :: Proxy (c :: * -> Constraint) -> ()
                           f _ = () in
                       [f (Proxy :: Proxy Eq), f (Proxy :: Proxy Show)] |]
test32_tylit = [| let f :: Proxy (a :: Symbol) -> Proxy (b :: Nat) -> ()
                      f _ _ = () in
                  f (Proxy :: Proxy "Hi there!") (Proxy :: Proxy 10) |]
test33_tvbs = [| let f :: forall a (b :: * -> *). Monad b => a -> b a
                     f = return in
                 [f 1, f 2] :: [Maybe Int] |]

test34_let_as = [| let a@(Just x) = Just 5 in
                   show x ++ show a |]

type Pair a = (a, a)
test35_expand = [| let f :: Pair a -> a
                       f = fst in
                   f |]

type Const a b = b
test36_expand = [| let f :: Const Int (,) Bool Char -> Char
                       f = snd in
                   f |]

type family TFExpand x
type instance TFExpand Int = Bool
type instance TFExpand (Maybe a) = [a]
test_expand3 = [| let f :: TFExpand Int -> ()
                      f True = () in
                  f |]
test_expand4 = [| let f :: TFExpand (Maybe Bool) -> ()
                      f [True, False] = () in
                  f |]

#if __GLASGOW_HASKELL__ >= 709
test37_pred = [| let f :: (Read a, (Show a, Num a)) => a -> a
                     f x = read (show x) + x in
                 (f 3, f 4.5) |]

test38_pred2 = [| let f :: a b => Proxy a -> b -> b
                      f _ x = x in
                  (f (Proxy :: Proxy Show) False, f (Proxy :: Proxy Num) (3 :: Int)) |]

test39_eq = [| let f :: (a ~ b) => a -> b
                   f x = x in
               (f ()) |]
#endif

#if __GLASGOW_HASKELL__ < 707
dec_test_nums = [1..9] :: [Int]
#else
dec_test_nums = [1..10] :: [Int]
#endif

dectest1 = [d| data Dec1 = Foo | Bar Int |]
dectest2 = [d| data Dec2 a = forall b. (Show b, Eq a) => MkDec2 a b Bool |]
dectest3 = [d| data Dec3 a = forall b. MkDec3 { foo :: a, bar :: b }
#if __GLASGOW_HASKELL__ >= 707
               type role Dec3 nominal
#endif
               |]
dectest4 = [d| newtype Dec4 a = MkDec4 (a, Int) |]
dectest5 = [d| type Dec5 a b = (a b, Maybe b) |]
dectest6 = [d| class (Monad m1, Monad m2) => Dec6 (m1 :: * -> *) m2 | m1 -> m2  where
                 lift :: forall a. m1 a -> m2 a
                 type M2 m1 :: * -> * |]
dectest7 = [d| type family Dec7 a (b :: *) (c :: Bool) :: * -> * |]
dectest8 = [d| type family Dec8 a |]
dectest9 = [d| data family Dec9 a (b :: * -> *) :: * -> * |]
#if __GLASGOW_HASKELL__ < 707
ds_dectest10 = DClosedTypeFamilyD (mkName "Dec10")
                                 [DPlainTV (mkName "a")]
                                 (Just (DArrowK DStarK DStarK))
                                 [ DTySynEqn [DConT ''Int]  (DConT ''Maybe)
                                 , DTySynEqn [DConT ''Bool] (DConT ''[]) ]
dectest10 = [d| type family Dec10 a :: * -> *
                type instance Dec10 Int = Maybe
                type instance Dec10 Bool = [] |]

ds_role_test = DRoleAnnotD (mkName "Dec3") [NominalR]
role_test = []
#else
dectest10 = [d| type family Dec10 a :: * -> * where
                  Dec10 Int = Maybe
                  Dec10 Bool = [] |]
#endif

instance_test = [d| instance (Show a, Show b) => Show (a -> b) where
                       show _ = "function" |]

class Dec6 a b where { lift :: a x -> b x; type M2 a }
imp_inst_test1 = [d| instance Dec6 Maybe (Either ()) where
                       lift Nothing = Left ()
                       lift (Just x) = Right x
                       type M2 Maybe = Either () |]

data family Dec9 a (b :: * -> *) :: * -> *
imp_inst_test2 = [d| data instance Dec9 Int Maybe a = MkIMB [a] | forall b. MkIMB2 (b a) |]
imp_inst_test3 = [d| newtype instance Dec9 Bool m x = MkBMX (m x) |]

type family Dec8 a
imp_inst_test4 = [d| type instance Dec8 Int = Bool |]

-- used for bug8884 test
type family Poly (a :: k) :: *
type instance Poly x = Int

flatten_dvald_test = [| let (a,b,c) = ("foo", 4, False) in
                        show a ++ show b ++ show c |]

rec_sel_test = [d| data RecordSel a = forall b. (Show a, Eq b) =>
                                      MkRecord { recsel1 :: (Int, a)
                                            , recsel_naughty :: (a, b)
                                            , recsel2 :: (forall b. b -> a)
                                            , recsel3 :: Bool }
                                    | MkRecord2 { recsel4 :: (a, a) } |]
rec_sel_test_num_sels = 4 :: Int   -- exclude naughty one

testRecSelTypes :: Int -> Q Exp
testRecSelTypes n = do
  VarI _ ty1 _ _ <- reify (mkName ("Test.DsDec.recsel" ++ show n))
  VarI _ ty2 _ _ <- reify (mkName ("Test.Dec.recsel"   ++ show n))
  let ty1' = return $ unqualify ty1
      ty2' = return $ unqualify ty2
  [| let x :: $ty1'
         x = undefined
         y :: $ty2'
         y = undefined
     in
     $(return $ VarE $ mkName "hasSameType") x y |]

  
-- used for expand


reifyDecs :: Q [Dec]
reifyDecs = [d|
  r1 :: a -> a
  r1 x = x

  class R2 a b where
    r3 :: a -> b -> c -> a
    type R4 b a c :: *
    data R5 a :: *

  data R6 a = R7 { r8 :: a -> a, r9 :: Bool }

  instance R2 (R6 a) a where
    r3 = undefined
    type R4 a (R6 a) c = a
    data R5 (R6 a) = forall b. Show b => R10 { r11 :: a, naughty :: b }

  type family R12 a b :: *

  data family R13 a :: *

  data instance R13 Int = R14 { r15 :: Bool }

  r16, r17 :: Int
  (r16, r17) = (5, 6)

  newtype R18 = R19 Bool

  type R20 = Bool

  type family R21 (a :: k) (b :: k) :: k where R21 a b = b
  |]

reifyDecsNames :: [Name]
reifyDecsNames = map mkName
  [ "r1", "R2", "r3", "R4", "R5", "R6", "R7", "r8", "r9", "R10", "r11"
  , "R12", "R13", "R14", "r15", "r16", "r17", "R18", "R19", "R20", "R21" ]
