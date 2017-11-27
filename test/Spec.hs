{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Test.QuickCheck
import Data.Word
import Data.Monoid
import Data.DisjointSet (DisjointSet)
import Data.DisjointMap (DisjointMap)
import Data.Set (Set)
import Data.Foldable (toList)
import Test.QuickCheck.Classes (jsonProps)
import Data.Proxy (Proxy(..))
import Data.Aeson (ToJSON,FromJSON)
import qualified Data.Foldable as F
import qualified Data.Set as S
import qualified Data.DisjointSet as DS
import qualified Data.DisjointMap as DM
import qualified GHC.OldList as L

main :: IO ()
main = do
  putStrLn "\nBeginning QuickCheck Tests"
  quickCheck propUnionAll
  quickCheck propUnionAppend
  quickCheck propSingletons
  quickCheck propEquivalances
  quickCheck propMapUnionAppend
  putStrLn "* Disjoint Set JSON"
  F.forM_ (jsonProps (Proxy :: Proxy (DisjointSet Word8))) $ \(name,p) -> do
    putStrLn name
    quickCheck p
  putStrLn "* Disjoint Map JSON"
  F.forM_ (jsonProps (Proxy :: Proxy (DisjointMap Word8 WrapWord8))) $ \(name,p) -> do
    putStrLn name
    quickCheck p

propUnionAll :: [Word] -> Bool
propUnionAll xs =
  let pairs = zip xs (drop 1 xs)
      ds = L.foldl' (\s (a,b) -> DS.union a b s) DS.empty pairs
      roots = mapM (\x -> DS.representative x ds) xs
   in case roots of
        Nothing -> L.length xs == 1
        Just [] -> L.null xs
        Just (y : ys) -> L.all (== y) ys

propUnionAppend :: [(Word,Word)] -> Bool
propUnionAppend xs = 
  let r1 = unionPairs xs
      (xs1,xs2) = splitList xs
      r2 = unionPairs xs1 <> unionPairs xs2
   in r1 == r2

propMapUnionAppend :: [(Word,Word)] -> [(Word,Sum Word)] -> Bool
propMapUnionAppend xs ys = 
  let r1 = unionMapPairs xs <> mapFromPairs ys
      (xs1,xs2) = splitList xs
      (ys1,ys2) = splitList ys
      r2 = unionMapPairs xs1 <> mapFromPairs ys1 <> unionMapPairs xs2 <> mapFromPairs ys2
   in r1 == r2

propSingletons :: [Set Word] -> Bool
propSingletons xs = foldMap unionFoldable xs == foldMap DS.singletons xs

propEquivalances :: [(Word,Word)] -> Bool
propEquivalances xs =
  let s = foldMap (\(a,b) -> DS.singletons (S.fromList [a,b])) xs
      All r = foldMap (\(a,b) -> All $ DS.equivalences a s == DS.equivalences b s) xs
   in r

splitList :: [a] -> ([a],[a])
splitList xs =
  let halfLen = div (L.length xs) 2
      xs1 = L.drop halfLen xs
      xs2 = L.take halfLen xs
   in (xs1,xs2)

unionFoldable :: Ord a => Foldable t => t a -> DisjointSet a
unionFoldable xs =
  let ys = toList xs
      pairs = zip ys (drop 1 ys)
   in case ys of
        [] -> DS.empty
        z : _ -> unionPairsGo pairs (DS.singleton z)

mapFromPairs :: (Ord k, Monoid v) => Foldable t => t (k,v) -> DisjointMap k v
mapFromPairs = F.foldl' (\dm (k,v) -> DM.insert k v dm) DM.empty

unionPairs :: Ord a => [(a,a)] -> DisjointSet a
unionPairs xs = unionPairsGo xs DS.empty

unionPairsGo :: Ord a => [(a,a)] -> DisjointSet a -> DisjointSet a
unionPairsGo [] !ds = ds
unionPairsGo ((a,b):xs) !ds = unionPairsGo xs (DS.union a b ds)

unionMapPairs :: (Ord k, Monoid v) => [(k,k)] -> DisjointMap k v
unionMapPairs xs = unionMapPairsGo xs DM.empty

unionMapPairsGo :: (Ord k, Monoid v) => [(k,k)] -> DisjointMap k v -> DisjointMap k v
unionMapPairsGo [] !ds = ds
unionMapPairsGo ((a,b):xs) !ds = unionMapPairsGo xs (DM.union a b ds)

instance (Arbitrary a, Ord a) => Arbitrary (DisjointSet a) where
  arbitrary = do
    xs <- arbitrary
    ys <- arbitrary
    let s1 = foldMap (\(a,b) -> DS.doubleton a b) (xs :: [(a,a)])
        s2 = foldMap DS.singleton (ys :: [a])
    return (s1 <> s2)

instance (Arbitrary k, Ord k, Monoid v, Arbitrary v) => Arbitrary (DisjointMap k v) where
  arbitrary = do
    xs <- arbitrary
    ys <- arbitrary
    let s1 = foldMap (\(k,v) -> DM.singleton k v) (xs :: [(k,v)])
        s2 = foldMap (\(k1,k2) -> DM.union k1 k2 DM.empty) (ys :: [(k,k)])
    return (s1 <> s2)

newtype WrapWord8 = WrapWord8 Word8
  deriving (FromJSON,ToJSON,Show,Eq,Arbitrary,Ord)

instance Monoid WrapWord8 where
  mempty = WrapWord8 0
  mappend (WrapWord8 a) (WrapWord8 b) = WrapWord8 (a + b)

