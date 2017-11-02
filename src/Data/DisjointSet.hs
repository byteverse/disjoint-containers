{-# LANGUAGE BangPatterns #-}

module Data.DisjointSet
  ( DisjointSet
  , empty
  , singleton
  , union
  , lookup
  , toLists
  ) where

import Prelude hiding (lookup)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

data DisjointSet a = DisjointSet
  { parents :: !(Map a a)
  , ranks :: !(Map a Int)
  }

instance Ord a => Monoid (DisjointSet a) where
  mappend = append
  mempty = empty

instance (Show a, Ord a) => Show (DisjointSet a) where
  show = showDisjointSet

showDisjointSet :: (Show a, Ord a) => DisjointSet a -> String
showDisjointSet = show . toLists

toLists :: Ord a => DisjointSet a -> [[a]]
toLists = map S.toList . toSets

toSets :: Ord a => DisjointSet a -> [Set a]
toSets = M.elems . flatten

-- in the result of this, the key in the
-- map keeps everything separate.
flatten :: Ord a => DisjointSet a -> Map a (Set a)
flatten ds@(DisjointSet p _) = S.foldl'
  ( \m a -> case find a ds of
    Nothing -> error "DisjointSet flatten: invariant violated. missing key."
    Just b -> M.insertWith S.union b (S.singleton a) m
  ) M.empty (M.keysSet p)

data Pair a b = Pair !a !b

union :: Ord a => a -> a -> DisjointSet a -> DisjointSet a
union !x !y set = flip execState set $ runMaybeT $ do
  repx <- lift $ state $ lookupCompressAdd x
  repy <- lift $ state $ lookupCompressAdd y
  guard $ repx /= repy
  DisjointSet p r <- lift get
  let rankx = r M.! repx
  let ranky = r M.! repy
  lift $ put $! case compare rankx ranky of
    LT -> let p' = M.insert repx repy p
              r' = M.delete repx r
          in  DisjointSet p' r'
    GT -> let p' = M.insert repy repx p
              r' = M.delete repy r
          in  DisjointSet p' r'
    EQ -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (ranky + 1) r
          in  DisjointSet p' r'

lookup :: Ord a => a -> DisjointSet a -> Maybe a
lookup = find

{-| Insert x into the disjoint set.  If it is already a member,
    then do nothing, otherwise x has no equivalence relations.
    O(logn).
-}
insert :: Ord a => a -> DisjointSet a -> DisjointSet a
insert !x set@(DisjointSet p r) =
    let (l, p') = M.insertLookupWithKey (\_ _ old -> old) x x p
    in  case l of
          Just _  -> set
          Nothing ->
              let r' = M.insert x 0 r
              in  DisjointSet p' r'

{-| Create a disjoint set with one member. O(1). -}
singleton :: a -> DisjointSet a
singleton !x =
  let p = M.singleton x x
      r = M.singleton x 0
   in DisjointSet p r

empty :: DisjointSet a
empty = DisjointSet M.empty M.empty

append :: Ord a => DisjointSet a -> DisjointSet a -> DisjointSet a
append s1@(DisjointSet m1 _) s2@(DisjointSet m2 _) = if M.size m1 > M.size m2
  then appendParents s1 m2
  else appendParents s2 m1

appendParents :: Ord a => DisjointSet a -> Map a a -> DisjointSet a
appendParents = M.foldlWithKey' $ \ds x y -> if x == y
  then insert x ds
  else union x y ds

{-| Create a disjoint set where all members are equal. -}
singletons :: Eq a => Set a -> DisjointSet a
singletons s = case S.lookupMin s of
  Nothing -> empty
  Just x ->
    let p = M.fromSet (\_ -> x) s
        r = M.fromSet (\y -> if x == y then 1 else 0) s
    in DisjointSet p r

lookupCompress :: Ord a => a -> DisjointSet a -> (Maybe a, DisjointSet a)
lookupCompress !x set =
  case find x set of
    Nothing  -> (Nothing, set)
    Just rep -> let set' = compress rep x set
                in  set' `seq` (Just rep, set')

lookupCompressAdd :: Ord a => a -> DisjointSet a -> (a, DisjointSet a)
lookupCompressAdd !x set =
  case find x set of
    Nothing -> (x, insert x set)
    Just rep -> let set' = compress rep x set
                in  set' `seq` (rep, set')

find :: Ord a => a -> DisjointSet a -> Maybe a
find !x (DisjointSet p _) =
  do x' <- M.lookup x p
     return $! if x == x' then x' else find' x'
  where find' y = let y' = p M.! y
                  in  if y == y' then y' else find' y'

-- TODO: make this smarter about recreating the parents Map.
-- Currently, it will recreate it more often than needed.
compress :: Ord a => a -> a -> DisjointSet a -> DisjointSet a
compress !rep = helper
    where helper !x set@(DisjointSet p r)
              | x == rep  = set
              | otherwise = helper x' set'
              where x'    = p M.! x
                    set'  = let p' = M.insert x rep p
                            in  p' `seq` DisjointSet p' r

