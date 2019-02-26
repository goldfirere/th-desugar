{- Language/Haskell/TH/Desugar/OMapSetUtil.hs

(c) Daniel Wagner 2016-2018, Ryan Scott 2019
-}
module Language.Haskell.TH.Desugar.OMapSetUtil where

import Data.Map (Map)
import qualified Data.Map as M

-- | An internal index used to track ordering only -- its magnitude doesn't
-- matter. If you manage to see this documentation, the library author has made
-- a mistake!
type Tag = Int

-- | A 0-based index, much like the indices used by lists' '!!' operation. All
-- indices are with respect to insertion order.
type Index = Int

nextLowerTag, nextHigherTag :: Map Tag a -> Tag
nextLowerTag  = maybe 0 pred . minTag
nextHigherTag = maybe 0 succ . maxTag

minTag, maxTag :: Map Tag a -> Maybe Tag
minTag m = fmap (fst . fst) (M.minViewWithKey m)
maxTag m = fmap (fst . fst) (M.maxViewWithKey m)

showsPrecList :: Show a => (b -> [a]) -> Int -> b -> ShowS
showsPrecList toList d o = showParen (d > 10) $
    showString "fromList " . shows (toList o)

readsPrecList :: Read a => ([a] -> b) -> Int -> ReadS b
readsPrecList fromList d = readParen (d > 10) $ \r -> do
    ("fromList", s) <- lex r
    (xs, t) <- reads s
    return (fromList xs, t)
