{- Language/Haskell/TH/Desugar/OMap/Internal.hs

(c) Daniel Wagner 2016-2018, Ryan Scott 2019
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
module Language.Haskell.TH.Desugar.OMap.Internal where

import Control.Monad (guard)
import Data.Data
import Data.Foldable (foldl')
import Data.Function (on)
import Data.Map (Map)
import Language.Haskell.TH.Desugar.OMapSetUtil (Index, Tag, maxTag, minTag, nextHigherTag, nextLowerTag, readsPrecList, showsPrecList)
import Prelude hiding (filter, lookup, null)
import qualified Data.Map as M

#if !(MIN_VERSION_base(4,8,0))
import Data.Foldable (Foldable, foldMap)
import Data.Monoid (Monoid(..))
#endif

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif

data OMap k v = OMap !(Map k (Tag, v)) !(Map Tag (k, v))

instance Functor (OMap k) where
  fmap f (OMap tvs kvs) = OMap (fmap (\(t, v) -> (t, f v)) tvs)
                               (fmap (\(k, v) -> (k, f v)) kvs)
-- | Values are produced in insertion order, not key order.
instance Foldable (OMap k) where foldMap f (OMap _ kvs) = foldMap (f . snd) kvs
instance (       Eq   k, Eq   v) => Eq   (OMap k v) where (==)    = (==)    `on` assocs
instance (       Ord  k, Ord  v) => Ord  (OMap k v) where compare = compare `on` assocs
instance (       Show k, Show v) => Show (OMap k v) where showsPrec = showsPrecList assocs
instance (Ord k, Read k, Read v) => Read (OMap k v) where readsPrec = readsPrecList fromList
instance Ord k => Semigroup (OMap k v) where
  (<>) = (|<>)
instance Ord k => Monoid (OMap k v) where
  mempty = empty
#if !(MIN_VERSION_base(4,11,0))
  mappend = (<>)
#endif

# if __GLASGOW_HASKELL__ >= 708
deriving instance Typeable OMap
# else
deriving instance Typeable2 OMap
# endif

-- This instance preserves data abstraction at the cost of inefficiency.
-- We provide limited reflection services for the sake of data abstraction.

instance (Data k, Data a, Ord k) => Data (OMap k a) where
  gfoldl f z m   = z fromList `f` assocs m
  toConstr _     = fromListConstr
  gunfold k z c  = case constrIndex c of
    1 -> k (z fromList)
    _ -> error "gunfold"
  dataTypeOf _   = oMapDataType
  dataCast2 f    = gcast2 f

fromListConstr :: Constr
fromListConstr = mkConstr oMapDataType "fromList" [] Prefix

oMapDataType :: DataType
oMapDataType = mkDataType "Data.Map.Ordered.Map" [fromListConstr]

infixr 5 <|, |< -- copy :
infixl 5 >|, |>
infixr 6 <>|, |<> -- copy <>

(<|) , (|<)  :: Ord k => (,)  k v -> OMap k v -> OMap k v
(>|) , (|>)  :: Ord k => OMap k v -> (,)  k v -> OMap k v
(<>|), (|<>) :: Ord k => OMap k v -> OMap k v -> OMap k v

(k, v) <| OMap tvs kvs = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = maybe (nextLowerTag kvs) fst (M.lookup k tvs)

(k, v) |< o = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = nextLowerTag kvs
    OMap tvs kvs = delete k o

o >| (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = nextHigherTag kvs
    OMap tvs kvs = delete k o

OMap tvs kvs |> (k, v) = OMap (M.insert k (t, v) tvs) (M.insert t (k, v) kvs) where
    t = maybe (nextHigherTag kvs) fst (M.lookup k tvs)

o <>| o' = unsafeMappend (o \\ o') o'
o |<> o' = unsafeMappend o (o' \\ o)

-- assumes that ts and ts' have disjoint keys
unsafeMappend :: Ord k => OMap k v -> OMap k v -> OMap k v
unsafeMappend (OMap ts vs) (OMap ts' vs')
    = OMap (M.union tsBumped tsBumped')
           (M.union vsBumped vsBumped')
    where
    bump  = case maxTag vs  of
        Nothing -> 0
        Just k  -> -k-1
    bump' = case minTag vs' of
        Nothing -> 0
        Just k  -> -k
    tsBumped  = fmap (\(t, v) -> (bump + t, v)) ts
    tsBumped' = fmap (\(t, v) -> (bump'+ t, v)) ts'
    vsBumped  = (bump +) `M.mapKeysMonotonic` vs
    vsBumped' = (bump'+) `M.mapKeysMonotonic` vs'

-- | @m \\\\ n@ deletes all the keys that exist in @n@ from @m@
(\\) :: Ord k => OMap k v -> OMap k v' -> OMap k v
o@(OMap _ _) \\ o'@(OMap _ _) = if size o < size o'
    then filter (const . (`notMember` o')) o
    else foldr delete o (fmap fst (assocs o'))

empty :: OMap k v
empty = OMap M.empty M.empty

-- | If a key appears multiple times, the first occurrence is used for ordering
-- and the last occurrence is used for its value. The library author welcomes
-- comments on whether this default is sane.
fromList :: Ord k => [(k, v)] -> OMap k v
fromList = foldl' (|>) empty

null :: OMap k v -> Bool
null (OMap tvs _) = M.null tvs

size :: OMap k v -> Int
size (OMap tvs _) = M.size tvs

member, notMember :: Ord k => k -> OMap k v -> Bool
member    k (OMap tvs _) = M.member    k tvs
notMember k (OMap tvs _) = M.notMember k tvs

lookup :: Ord k => k -> OMap k v -> Maybe v
lookup k (OMap tvs _) = fmap snd (M.lookup k tvs)

-- The Ord constraint is for compatibility with older (<0.5) versions of
-- containers.
-- | @filter f m@ contains exactly the key-value pairs of @m@ that satisfy @f@,
-- without changing the order they appear
filter :: Ord k => (k -> v -> Bool) -> OMap k v -> OMap k v
filter f (OMap tvs kvs) = OMap (M.filterWithKey (\k (_, v) -> f k v) tvs)
                               (M.filterWithKey (\_ (k, v) -> f k v) kvs)

delete :: Ord k => k -> OMap k v -> OMap k v
delete k o@(OMap tvs kvs) = case M.lookup k tvs of
    Nothing     -> o
    Just (t, _) -> OMap (M.delete k tvs) (M.delete t kvs)

findIndex :: Ord k => k -> OMap k v -> Maybe Index
findIndex k (OMap tvs kvs) = do
    (t, _) <- M.lookup k tvs
    M.lookupIndex t kvs

elemAt :: OMap k v -> Index -> Maybe (k, v)
elemAt (OMap _ kvs) i = do
    guard (0 <= i && i < M.size kvs)
    return . snd $ M.elemAt i kvs

-- | Return key-value pairs in the order they were inserted.
assocs :: OMap k v -> [(k, v)]
assocs (OMap _ kvs) = map snd $ M.toAscList kvs

-- | Return key-value pairs in order of increasing key.
toAscList :: OMap k v -> [(k, v)]
toAscList (OMap tvs _) = map (\(k, (_, v)) -> (k, v)) $ M.toAscList tvs
