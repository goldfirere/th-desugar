{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, MagicHash, UnboxedTuples,
             MultiWayIf, ParallelListComp, CPP, BangPatterns,
             ScopedTypeVariables, RankNTypes, TypeFamilies, ImpredicativeTypes,
             DataKinds, PolyKinds, GADTs, MultiParamTypeClasses,
             FunctionalDependencies, FlexibleInstances, StandaloneDeriving,
             DefaultSignatures, ConstraintKinds, GADTs, ViewPatterns,
             TupleSections, NoMonomorphismRestriction #-}

#if __GLASGOW_HASKELL__ >= 711
{-# LANGUAGE TypeApplications #-}
#endif

#if __GLASGOW_HASKELL__ >= 801
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UnboxedSums #-}
#endif

#if __GLASGOW_HASKELL__ >= 803
{-# LANGUAGE OverloadedLabels #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- IsLabel is an orphan
#endif

#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE QuantifiedConstraints #-}
#endif

#if __GLASGOW_HASKELL__ >= 807
{-# LANGUAGE ImplicitParams #-}
#endif

#if __GLASGOW_HASKELL__ >= 809
{-# LANGUAGE StandaloneKindSignatures #-}
#endif

{-# OPTIONS_GHC -fno-warn-missing-signatures -fno-warn-type-defaults
                -fno-warn-name-shadowing #-}

module Splices where

import Data.List
import Data.Char
import GHC.Exts
import GHC.TypeLits

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Syntax (Quasi)
import Data.Generics

#if __GLASGOW_HASKELL__ >= 803
import GHC.OverloadedLabels ( IsLabel(..) )
#endif

dsSplice :: Q Exp -> Q Exp
dsSplice expq = expq >>= dsExp >>= (return . expToTH)

dsDecSplice :: Q [Dec] -> Q [Dec]
dsDecSplice decsQ = decsQ >>= dsDecs >>= (return . decsToTH)

testDecSplice :: Int -> Q Exp
testDecSplice n = do
  let dsName  = mkName $ "DsDec.Dec" ++ show n
      regName = mkName $ "Dec.Dec" ++ show n
  infoDs  <- reify dsName
  infoReg <- reify regName
  rolesDs  <- reifyRoles dsName
  rolesReg <- reifyRoles regName
#if __GLASGOW_HASKELL__ < 711
  eqTHSplice (infoDs, rolesDs) (infoReg, rolesReg)
#else
  fixityDs  <- reifyFixity dsName
  fixityReg <- reifyFixity regName
  eqTHSplice (infoDs, rolesDs, fixityDs) (infoReg, rolesReg, fixityReg)
#endif

unqualify :: Data a => a -> a
unqualify = everywhere (mkT (mkName . nameBase))

assumeStarT :: Data a => a -> a
#if __GLASGOW_HASKELL__ < 709
assumeStarT = id
#else
assumeStarT = everywhere (mkT go)
  where
    go :: TyVarBndr -> TyVarBndr
    go (PlainTV n) = KindedTV n StarT
    go (KindedTV n k) = KindedTV n (assumeStarT k)
#endif

dropTrailing0s :: Data a => a -> a
dropTrailing0s = everywhere (mkT (mkName . frob . nameBase))
  where
    frob str
      | head str == 'r' = str
      | head str == 'R' = str
      | otherwise       = dropWhileEnd isDigit str

eqTH :: (Data a, Show a) => a -> a -> Bool
eqTH a b = show (unqualify a) == show (unqualify b)

eqTHSplice :: (Quasi q, Data a, Show a) => a -> a -> q Exp
eqTHSplice a b = runQ $
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
test11_parcomp = [| [ (x,y) | x <- [1..10], x `mod` 2 == 0 | y <- [2,5..20] ] |]
test12_parcomp2 = [| [ (x,y,z) | x <- [1..10], z <- [3..100], x + z `mod` 2 == 0 | y <- [2,5..20] ] |]
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
#if __GLASGOW_HASKELL__ >= 801
test23_sigp = [| map (\ (a :: Int) -> a + a) [5, 10] |]
#endif

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
                  (f (Proxy :: Proxy 'False), f (Proxy :: Proxy 'True)) |]
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

type Constant a b = b
test36_expand = [| let f :: Constant Int (,) Bool Char -> Char
                       f = snd in
                   f |]

#if __GLASGOW_HASKELL__ >= 711
test40_wildcards = [| let f :: (Show a, _) => a -> a -> _
                          f x y = if x == y then show x else "bad" in
                      f True False :: String |]
#endif

#if __GLASGOW_HASKELL__ >= 801
test41_typeapps = [| let f :: forall a. (a -> Bool) -> Bool
                         f g = g (undefined @_ @a) in
                     f (const True) |]

test42_scoped_tvs = [| let f :: (Read a, Show a) => a -> String -> String
                           f (_ :: b) (x :: String) = show (read x :: b)
                       in f True "True" |]

test43_ubx_sums = [| let f :: (# Bool | String #) -> Bool
                         f (# b |   #) = not b
                         f (#   | c #) = c == "c" in
                     f (# | "a" #) |]
#endif

test44_let_pragma = [| let x :: Int
                           x = 1
                           {-# INLINE x #-}
                       in x |]

test45_empty_record_con = [| let j :: Maybe Int
                                 j = Just{}
                             in case j of
                                Nothing -> j
                                Just{}  -> j |]

#if __GLASGOW_HASKELL__ >= 803
data Label (l :: Symbol) = Get

class Has a l b | a l -> b where
  from :: a -> Label l -> b

data Point = Point Int Int deriving Show

instance Has Point "x" Int where from (Point x _) _ = x
instance Has Point "y" Int where from (Point _ y) _ = y

instance Has a l b => IsLabel l (a -> b) where
  fromLabel x = from x (Get :: Label l)

test46_overloaded_label = [| let p = Point 3 4 in
                             #x p - #y p |]
#endif

test47_do_partial_match = [| do { Just () <- [Nothing]; return () } |]

#if __GLASGOW_HASKELL__ >= 805
test48_quantified_constraints =
  [| let f :: forall f a. (forall x. Eq x => Eq (f x), Eq a) => f a -> f a -> Bool
         f = (==)
     in f (Proxy @Int) (Proxy @Int) |]
#endif

#if __GLASGOW_HASKELL__ >= 807
test49_implicit_params = [| let f :: (?x :: Int, ?y :: Int) => (Int, Int)
                                f =
                                  let ?x = ?y
                                      ?y = ?x
                                  in (?x, ?y)
                            in (let ?x = 42
                                    ?y = 27
                                in f) |]

test50_vka = [| let hrefl :: (:~~:) @Bool @Bool 'True 'True
                    hrefl = HRefl
                in hrefl |]
#endif

#if __GLASGOW_HASKELL__ >= 809
test51_tuple_sections =
  [| let f1 :: String -> Char -> (String, Int, Char)
         f1 = (,5,)

         f2 :: String -> Char -> (# String, Int, Char #)
         f2 = (#,5,#)
     in case (#,#) (f1 "a" 'a') (f2 "b" 'b') of
          (#,#) ((,,) _ a _) ((#,,#) _ b _) -> a + b |]
#endif

type family TFExpand x
type instance TFExpand Int = Bool
type instance TFExpand (Maybe a) = [a]
test_expand3 = [| let f :: TFExpand Int -> ()
                      f True = () in
                  f |]
test_expand4 = [| let f :: TFExpand (Maybe Bool) -> ()
                      f [True, False] = () in
                  f |]

type family ClosedTF a where
  ClosedTF Int = Bool
  ClosedTF x   = Char

test_expand5 = [| let f :: ClosedTF Int -> ()
                      f True = () in
                  f |]
test_expand6 = [| let f :: ClosedTF Double -> ()
                      f 'x' = () in
                  f |]

#if __GLASGOW_HASKELL__ >= 809
type PolyTF :: forall k. k -> *
#endif
type family PolyTF (x :: k) :: * where
  PolyTF (x :: *) = Bool

test_expand7 = [| let f :: PolyTF Int -> ()
                      f True = () in
                  f |]
test_expand8 = [| let f :: PolyTF IO -> ()
                      f True = () in
                  f |]


#if __GLASGOW_HASKELL__ >= 709
test_expand9 = [| let f :: TFExpand (Maybe (IO a)) -> IO ()
                      f actions = sequence_ actions in
                  f |]
#endif

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

#if __GLASGOW_HASKELL__ < 709
dec_test_nums = [1..10] :: [Int]
#else
dec_test_nums = [1..11] :: [Int]
#endif

dectest1 = [d| data Dec1 where
                 Foo :: Dec1
                 Bar :: Int -> Dec1 |]
dectest2 = [d| data Dec2 a where
                 MkDec2 :: forall a b. (Show b, Eq a) => a -> b -> Bool -> Dec2 a |]
dectest3 = [d| data Dec3 a where
                 MkDec3 :: forall a b. { foo :: a, bar :: b } -> Dec3 a
               type role Dec3 nominal
               |]
dectest4 = [d| newtype Dec4 a where
                 MkDec4 :: (a, Int) -> Dec4 a |]
dectest5 = [d| type Dec5 a b = (a b, Maybe b) |]
dectest6 = [d| class (Monad m1, Monad m2) => Dec6 (m1 :: * -> *) m2 | m1 -> m2  where
                 lift :: forall a. m1 a -> m2 a
                 type M2 m1 :: * -> * |]
dectest7 = [d| type family Dec7 a (b :: *) (c :: Bool) :: * -> * |]
dectest8 = [d| type family Dec8 a |]
dectest9 = [d| data family Dec9 a (b :: * -> *) :: * -> * |]
dectest10 = [d| type family Dec10 a :: * -> * where
                  Dec10 Int = Maybe
                  Dec10 Bool = [] |]

data Blarggie a = MkBlarggie Int a
#if __GLASGOW_HASKELL__ >= 709
dectest11 = [d| class Dec11 a where
                  meth13 :: a -> a -> Bool
                  default meth13 :: Eq a => a -> a -> Bool
                  meth13 = (==)
              |]
standalone_deriving_test = [d| deriving instance Eq a => Eq (Blarggie a) |]
#endif
#if __GLASGOW_HASKELL__ >= 801
deriv_strat_test = [d| deriving stock instance Ord a => Ord (Blarggie a) |]
#endif

dectest12 = [d| data Dec12 a where
                  MkGInt :: Dec12 Int
                  MkGOther :: Dec12 b

              |]

dectest13 = [d| data Dec13 :: (* -> Constraint) -> * where
                  MkDec13 :: c a => a -> Dec13 c
              |]

dectest14 = [d| data InfixADT = Int `InfixADT` Int |]

dectest15 = [d| infixl 5 :**:, :&&:, :^^:, `ActuallyPrefix`
                data InfixGADT a where
                  (:**:) :: Int -> b -> InfixGADT (Maybe b) -- Only this one is infix
                  (:&&:) :: { infixGADT1 :: b, infixGADT2 :: Int } -> InfixGADT [b]
                  ActuallyPrefix :: Char -> Bool -> InfixGADT Double
                  (:^^:) :: Int -> Int -> Int -> InfixGADT Int
                  (:!!:) :: Char -> Char -> InfixGADT Char |]

class ExCls a
data ExData1 a
data ExData2 a

ds_dectest16 = DInstanceD Nothing (Just [DPlainTV (mkName "a")]) []
                (DConT ''ExCls `DAppT`
                  (DConT ''ExData1 `DAppT` DVarT (mkName "a"))) []
dectest16 :: Q [Dec]
dectest16 = return [ InstanceD
#if __GLASGOW_HASKELL__ >= 800
                       Nothing
#endif
                       [] (ForallT [PlainTV (mkName "a")] []
                                   (ConT ''ExCls `AppT`
                                     (ConT ''ExData1 `AppT` VarT (mkName "a")))) [] ]
ds_dectest17 = DStandaloneDerivD Nothing (Just [DPlainTV (mkName "a")]) []
                (DConT ''ExCls `DAppT`
                  (DConT ''ExData2 `DAppT` DVarT (mkName "a")))
#if __GLASGOW_HASKELL__ >= 710
dectest17 :: Q [Dec]
dectest17 = return [ StandaloneDerivD
#if __GLASGOW_HASKELL__ >= 802
                       Nothing
#endif
                       [] (ForallT [PlainTV (mkName "a")] []
                                   (ConT ''ExCls `AppT`
                                     (ConT ''ExData2 `AppT` VarT (mkName "a")))) ]
#endif

#if __GLASGOW_HASKELL__ >= 809
dectest18 = [d| data Dec18 :: forall k -> k -> * where
                  MkDec18 :: forall k (a :: k). Dec18 k a |]
#endif

instance_test = [d| instance (Show a, Show b) => Show (a -> b) where
                       show _ = "function" |]

class Dec6 a b where { lift :: a x -> b x; type M2 a }
imp_inst_test1 = [d| instance Dec6 Maybe (Either ()) where
                       lift Nothing = Left ()
                       lift (Just x) = Right x
                       type M2 Maybe = Either () |]

data family Dec9 a (b :: * -> *) :: * -> *
#if __GLASGOW_HASKELL__ >= 800
imp_inst_test2 = [d| data instance Dec9 Int Maybe a where
                       MkIMB  ::             [a] -> Dec9 Int Maybe a
                       MkIMB2 :: forall a b. b a -> Dec9 Int Maybe a |]
imp_inst_test3 = [d| newtype instance Dec9 Bool m x where
                       MkBMX :: m x -> Dec9 Bool m x |]
#else
-- TH-quoted data family instances with GADT syntax are horribly broken on GHC 7.10
-- and older, so we opt to use non-GADT syntax on older GHCs so we can at least
-- test *something*.
imp_inst_test2 = [d| data instance Dec9 Int Maybe a = MkIMB [a] | forall b. MkIMB2 (b a) |]
imp_inst_test3 = [d| newtype instance Dec9 Bool m x = MkBMX (m x) |]
#endif

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
#if __GLASGOW_HASKELL__ > 710
  VarI _ ty1 _ <- reify (mkName ("DsDec.recsel" ++ show n))
  VarI _ ty2 _ <- reify (mkName ("Dec.recsel"   ++ show n))
#else
  VarI _ ty1 _ _ <- reify (mkName ("DsDec.recsel" ++ show n))
  VarI _ ty2 _ _ <- reify (mkName ("Dec.recsel"   ++ show n))
#endif
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
  -- NB: Use a forall here! If you don't, when you splice r1 in and then reify
  -- it, GHC will add an explicit forall behind the scenes, which will cause an
  -- incongruity with the locally reified declaration (which would lack an
  -- explicit forall).
  r1 :: forall a. a -> a
  r1 x = x

  class R2 a b where
    r3 :: a -> b -> c -> a
    type R4 b a :: *
    data R5 a :: *

  data R6 a = R7 { r8 :: a -> a, r9 :: Bool }

  instance R2 (R6 a) a where
    r3 = undefined
    type R4 a (R6 a) = a
    data R5 (R6 a) = forall b. Show b => R10 { r11 :: a, naughty :: b }

  type family R12 a b :: *

  data family R13 a :: *

  data instance R13 Int = R14 { r15 :: Bool }

  r16, r17 :: Int
  (r16, r17) = (5, 6)

  newtype R18 = R19 Bool

  type R20 = Bool
  type family R21 (a :: k) (b :: k) :: k where
#if __GLASGOW_HASKELL__ >= 801
#if __GLASGOW_HASKELL__ >= 807
    forall k (a :: k) (b :: k).
#endif
      R21 (a :: k) (b :: k) = b
#else
    -- Due to GHC Trac #12646, R21 will get reified without kind signatures on
    -- a and b on older GHCs, so we must reflect that here.
    R21 a b = b
#endif
  class XXX a where
    r22 :: a -> a
    r22 = id   -- test #32

  data R23 a = MkR23 { getR23 :: a }

  r23Test :: R23 a -> a
  r23Test (MkR23 { getR23 = x }) = x

#if __GLASGOW_HASKELL__ >= 801
  pattern Point :: Int -> Int -> (Int, Int)
  pattern Point{x, y} = (x, y)

  data T a where
    MkT :: Eq b => a -> b -> T a

  foo :: Show a => a -> Bool
  foo x = show x == "foo"

  pattern P :: Show a => Eq b => b -> T a
  pattern P x <- MkT (foo -> True) x

  pattern HeadC :: a -> [a]
  pattern HeadC x <- x:_ where
    HeadC x = [x]

  class LL f where
    llMeth :: f a -> ()

  instance LL [] where
    llMeth _ = ()

  pattern LLMeth :: LL f => f a
  pattern LLMeth <- (llMeth -> ())

  {-# COMPLETE LLMeth :: [] #-}

  llEx :: [a] -> Int
  llEx LLMeth = 5
#endif

#if __GLASGOW_HASKELL__ >= 805
  newtype Id a = MkId a
    deriving stock Eq

  newtype R24 a = MkR24 [a]
    deriving Eq via (Id [a])
#endif

#if __GLASGOW_HASKELL__ >= 800
  class R25 (f :: k -> *) where
    r26 :: forall (a :: k). f a

  data R27 (a :: k) = R28 { r29 :: Proxy a }
#endif

  class R30 a where
    r31 :: a -> b -> a

#if __GLASGOW_HASKELL__ >= 809
  type R32 :: forall k -> k -> *
  type family R32 :: forall k -> k -> * where
#endif

  data R33 a where
    R34 :: { r35 :: Int } -> R33 Int
  |]

reifyDecsNames :: [Name]
reifyDecsNames = map mkName
  [ "r1"
#if __GLASGOW_HASKELL__ < 711
  , "R2", "r3"      -- these fail due to GHC#11797
#endif
  , "R4", "R5", "R6", "R7", "r8", "r9", "R10", "r11"
  , "R12", "R13", "R14", "r15", "r16", "r17", "R18", "R19", "R20"
  , "R21"
  , "r22"
#if __GLASGOW_HASKELL__ >= 800
  , "R25", "r26", "R28", "r29"
#endif
  , "R30", "r31"
#if __GLASGOW_HASKELL__ >= 809
  , "R32"
#endif
  , "R33", "R34", "r35"
  ]

simplCaseTests :: [Q Exp]
simplCaseTests =
  [ [| map (\a -> case a :: [Int] of
        (_:_:_:_) -> (5 :: Int)
        _         -> 6) [[], [1], [1,2,3]]
     |]
  , [| let foo [] = True
           foo _  = False in (foo [], foo "hi") |]
#if __GLASGOW_HASKELL__ >= 801
  , [| let foo ([] :: String) = True
           foo (_  :: String) = False
        in foo "hello" |]
#endif
  ]

-- These foralls are needed because of bug trac9262, fixed in ghc-7.10.
round_trip_types :: [TypeQ]
round_trip_types =
    [ [t|forall a. a ~ Int => a|]
    , [t|forall a. [a]|]
    , [t|forall a b. (a,b)|] ]

test_exprs :: [Q Exp]
test_exprs = [ test1_sections
             , test2_lampats
             , test3_lamcase
-- see above             , test4_tuples
             , test5_ifs
             , test6_ifs2
             , test7_let
             , test8_case
             , test9_do
             , test10_comp
             , test11_parcomp
             , test12_parcomp2
             , test13_sig
             , test14_record
             , test15_litp
             , test16_tupp
             , test17_infixp
             , test18_tildep
             , test19_bangp
             , test20_asp
             , test21_wildp
             , test22_listp
#if __GLASGOW_HASKELL__ >= 801
             , test23_sigp
#endif
             , test24_fun
             , test25_fun2
             , test26_forall
             , test27_kisig
             , test28_tupt
             , test29_listt
             , test30_promoted
             , test31_constraint
             , test32_tylit
             , test33_tvbs
             , test34_let_as
#if __GLASGOW_HASKELL__ >= 709
             , test37_pred
             , test38_pred2
             , test39_eq
#endif
#if __GLASGOW_HASKELL__ >= 801
             , test41_typeapps
             , test42_scoped_tvs
             , test43_ubx_sums
#endif
             , test44_let_pragma
             , test45_empty_record_con
#if __GLASGOW_HASKELL__ >= 803
             , test46_overloaded_label
#endif
             , test47_do_partial_match
#if __GLASGOW_HASKELL__ >= 805
             , test48_quantified_constraints
#endif
#if __GLASGOW_HASKELL__ >= 807
             , test49_implicit_params
             , test50_vka
#endif
#if __GLASGOW_HASKELL__ >= 809
             , test51_tuple_sections
#endif
             ]
