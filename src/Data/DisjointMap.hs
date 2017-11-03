{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

{-# OPTIONS_GHC -Wall #-}

module Data.DisjointMap
  ( DisjointMap
    -- * Construction
  , empty
  , singleton
  , singletons
  , insert
  , union
    -- * Query
  , lookup
  , representative
  , representative'
    -- * Conversion
  , toLists
  ) where

import Prelude hiding (lookup)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad

import Data.Map (Map)
import Data.Set (Set)
import Data.Bifunctor (first)
import Data.Foldable (Foldable)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Set as S

-- | A map having disjoints sets of @k@ as keys and
--   @v@ as values.
data DisjointMap k v = DisjointMap
  !(Map k k) -- parents and values
  !(Map k (Ranked v)) -- ranks
  deriving (Functor,Foldable,Traversable)

data Ranked b = Ranked {-# UNPACK #-} !Int !b
  deriving (Functor,Foldable,Traversable)

instance (Ord k, Monoid v) => Monoid (DisjointMap k v) where
  mappend = append
  mempty = empty

-- technically, it should be possible to weaken the Ord constraint on v to
-- an Eq constraint
instance (Ord k, Ord v) => Eq (DisjointMap k v) where
  a == b = S.fromList (toSets a) == S.fromList (toSets b)

instance (Ord k, Ord v) => Ord (DisjointMap k v) where
  compare a b = compare (S.fromList (toSets a)) (S.fromList (toSets b))

instance (Show k, Ord k, Show v) => Show (DisjointMap k v) where
  show = showDisjointSet

showDisjointSet :: (Show k, Ord k, Show v) => DisjointMap k v -> String
showDisjointSet = show . toLists

toLists :: Ord k => DisjointMap k v -> [([k],v)]
toLists = (fmap.first) S.toList . toSets

toSets :: Ord k => DisjointMap k v -> [(Set k,v)]
toSets dm@(DisjointMap _ r) = M.elems $ MM.merge MM.dropMissing MM.dropMissing (MM.zipWithMatched $ \_ ks (Ranked _ v) -> (ks,v)) (flatten dm) r

-- in the result of this, the key in the
-- map keeps everything separate.
flatten :: Ord k => DisjointMap k v -> Map k (Set k)
flatten ds@(DisjointMap p _) = S.foldl'
  ( \m a -> case find a ds of
    Nothing -> error "DisjointMap flatten: invariant violated. missing key."
    Just b -> M.insertWith S.union b (S.singleton a) m
  ) M.empty (M.keysSet p)

{-|
Create an equivalence relation between x and y. If either x or y
are not already is the disjoint set, they are first created
as singletons with a value that is 'mempty'.
-}
union :: (Ord k, Monoid v) => k -> k -> DisjointMap k v -> DisjointMap k v
union !x !y set = flip execState set $ runMaybeT $ do
  repx <- lift $ state $ lookupCompressAdd x
  repy <- lift $ state $ lookupCompressAdd y
  guard $ repx /= repy
  DisjointMap p r <- lift get
  let Ranked rankx valx = r M.! repx
  let Ranked ranky valy = r M.! repy
  let val = mappend valx valy
  lift $ put $! case compare rankx ranky of
    LT -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (Ranked ranky val) r
          in  DisjointMap p' r'
    GT -> let p' = M.insert repy repx p
              r' = M.delete repy $! M.insert repx (Ranked rankx val) r
          in  DisjointMap p' r'
    EQ -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (Ranked (ranky + 1) val) r
          in  DisjointMap p' r'

{-|
Find the set representative for this input. This function
ignores the values in the map.
-}
representative :: Ord k => k -> DisjointMap k v -> Maybe k
representative = find

{-| Insert a key-value pair into the disjoint map. If the key
    is is already present in another set, combine the value
    monoidally with the value belonging to it.
    Otherwise, this creates a singleton set as a new key and
    associates it with the value.
-}
insert :: (Ord k, Monoid v) => k -> v -> DisjointMap k v -> DisjointMap k v
insert !x !v set@(DisjointMap p r) =
  let (l, p') = M.insertLookupWithKey (\_ _ old -> old) x x p
   in case l of
        Just _ ->
          let (m,DisjointMap p2 r') = representative' x set
           in case m of
                Nothing -> error "DisjointMap insert: invariant violated"
                Just root -> DisjointMap p2 (M.adjust (\(Ranked rank vOld) -> Ranked rank (mappend v vOld)) root r')
        Nothing ->
          let r' = M.insert x (Ranked 0 v) r
          in  DisjointMap p' r'

{-| Create a disjoint map with one key: a singleton set. O(1). -}
singleton :: k -> v -> DisjointMap k v
singleton !x !v =
  let p = M.singleton x x
      r = M.singleton x (Ranked 0 v)
   in DisjointMap p r

{-| The empty map -}
empty :: DisjointMap k v
empty = DisjointMap M.empty M.empty

append :: (Ord k, Monoid v) => DisjointMap k v -> DisjointMap k v -> DisjointMap k v
append s1@(DisjointMap m1 r1) s2@(DisjointMap m2 r2) = if M.size m1 > M.size m2
  then appendParents r2 s1 m2
  else appendParents r1 s2 m1

appendParents :: (Ord k, Monoid v) => Map k (Ranked v) -> DisjointMap k v -> Map k k -> DisjointMap k v
appendParents !ranks = M.foldlWithKey' $ \ds x y -> if x == y
  then case M.lookup x ranks of
    Nothing -> error "DisjointMap appendParents: invariant violated"
    Just (Ranked _ v) -> insert x v ds
  else union x y ds

{-| Create a disjoint map with one key. Everything in the
    'Set' argument is consider part of the same equivalence
    class.
-}
singletons :: Eq k => Set k -> v -> DisjointMap k v
singletons s v = case S.lookupMin s of
  Nothing -> empty
  Just x ->
    let p = M.fromSet (\_ -> x) s
        r = M.singleton x (Ranked 1 v)
    in DisjointMap p r

{-|
Find the set representative for this input. Returns a new disjoint
set in which the path has been compressed.
-}
representative' :: Ord k => k -> DisjointMap k v -> (Maybe k, DisjointMap k v)
representative' !x set =
  case find x set of
    Nothing  -> (Nothing, set)
    Just rep -> let set' = compress rep x set
                in  set' `seq` (Just rep, set')

lookupCompressAdd :: (Ord k, Monoid v) => k -> DisjointMap k v -> (k, DisjointMap k v)
lookupCompressAdd !x set =
  case find x set of
    Nothing -> (x, insert x mempty set)
    Just rep -> let set' = compress rep x set
                in  set' `seq` (rep, set')

find :: Ord k => k -> DisjointMap k v -> Maybe k
find !x (DisjointMap p _) =
  do x' <- M.lookup x p
     return $! if x == x' then x' else find' x'
  where find' y = let y' = p M.! y
                  in  if y == y' then y' else find' y'

{-| Find the value associated with the set containing
    the provided key.
-}
lookup :: Ord k => k -> DisjointMap k v -> Maybe v
lookup !x (DisjointMap p r) =
  do x' <- M.lookup x p
     if x == x'
       then case M.lookup x r of
         Nothing -> Nothing
         Just (Ranked _ v) -> Just v
       else find' x'
  where find' y = let y' = p M.! y
                   in if y == y'
                        then case M.lookup y r of
                          Nothing -> Nothing
                          Just (Ranked _ v) -> Just v
                        else find' y'

-- TODO: make this smarter about recreating the parents Map.
-- Currently, it will recreate it more often than needed.
compress :: Ord k => k -> k -> DisjointMap k v -> DisjointMap k v
compress !rep = helper
  where
  helper !x set@(DisjointMap p r)
    | x == rep  = set
    | otherwise = helper x' set'
    where x'    = p M.! x
          set'  = let p' = M.insert x rep p
                  in  p' `seq` DisjointMap p' r


