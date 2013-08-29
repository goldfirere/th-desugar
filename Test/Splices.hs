{- Tests for the th-desugar package

(c) Richard Eisenberg 2013
eir@cis.upenn.edu
-}

{-# LANGUAGE TemplateHaskell, LambdaCase, MagicHash, UnboxedTuples,
             MultiWayIf, ParallelListComp, CPP, BangPatterns,
             ScopedTypeVariables, RankNTypes, TypeFamilies, ImpredicativeTypes,
             DataKinds, PolyKinds #-}

module Test.Splices where

import Data.List

import Language.Haskell.TH
import Language.Haskell.TH.Desugar
import Language.Haskell.TH.Desugar.Sweeten

dsSplice :: Q Exp -> Q Exp
dsSplice expq = expq >>= dsExp >>= (return . expToTH)

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

data Proxy a = Proxy
  deriving Show
                
test27_kisig = [| let f :: Proxy (a :: Bool) -> ()
                      f _ = () in
                  (f (Proxy :: Proxy False), f (Proxy :: Proxy True)) |]
                      