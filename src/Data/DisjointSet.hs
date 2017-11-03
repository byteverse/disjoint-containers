{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wall #-}

{-|
Persistent disjoint-sets. Disjoint-sets are a set of elements 
with equivalence relations defined between elements, i.e. 
two elements may be members of the same equivalence set.
This library provides the fundamental operations classically
known as @union@, @find@, and @makeSet@. It also offers
novelties like a 'Monoid' instance for disjoint sets
and conversion functions for interoperating with lists.
See the tutorial at the bottom of this page for an example
of how to use this library.
-}

module Data.DisjointSet
  ( DisjointSet
    -- * Construction
  , empty
  , singleton
  , singletons
  , doubleton
  , insert
  , union
    -- * Query
  , equivalent
  , sets
  , values
  , representative
  , representative'
    -- * Conversion
  , toLists
  , pretty
    -- * Tutorial
    -- $tutorial
  ) where

import Prelude hiding (lookup)
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad

import Data.Map (Map)
import Data.Set (Set)
import Data.Semigroup (Semigroup)
import Data.Maybe (fromMaybe)
import qualified Data.Semigroup
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L

data DisjointSet a = DisjointSet
  !(Map a a) -- parents
  !(Map a Int) -- ranks

instance Ord a => Monoid (DisjointSet a) where
  mappend = append
  mempty = empty

instance Ord a => Semigroup (DisjointSet a) where
  (<>) = append

instance Ord a => Eq (DisjointSet a) where
  a == b = S.fromList (toSets a) == S.fromList (toSets b)

instance Ord a => Ord (DisjointSet a) where
  compare a b = compare (S.fromList (toSets a)) (S.fromList (toSets b))

instance (Show a, Ord a) => Show (DisjointSet a) where
  show = showDisjointSet

showDisjointSet :: (Show a, Ord a) => DisjointSet a -> String
showDisjointSet = show . toLists

pretty :: (Ord a, Show a) => DisjointSet a -> String
pretty xs = id
  . showChar '{'
  . applyList (L.intersperse (showChar ',') (map (\x -> showChar '{' . applyList (L.intersperse (showChar ',') (map shows x)) . showChar '}') (toLists xs)))
  . showChar '}'
  $ []

applyList :: [(a -> a)] -> a -> a
applyList [] = id
applyList (f : fs) = f . applyList fs

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

{-|
Create an equivalence relation between x and y. If either x or y
are not already is the disjoint set, they are first created
as singletons.
-}
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

{-|
Find the set representative for this input.
-}
representative :: Ord a => a -> DisjointSet a -> Maybe a
representative = find

{-| Decides whether the two values belong to the same set -}
equivalent :: Ord a => a -> a -> DisjointSet a -> Bool
equivalent a b ds = fromMaybe False $ do
  x <- representative a ds
  y <- representative b ds
  Just (x == y)

{-| Count the number of disjoint sets -}
sets :: DisjointSet a -> Int
sets (DisjointSet _ r) = M.size r

{-| Count the total number of values contained by the disjoint sets -}
values :: DisjointSet a -> Int
values (DisjointSet p _) = M.size p

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

{-| Create a disjoint set with a single set containing two members -}
doubleton :: Ord a => a -> a -> DisjointSet a
doubleton a b = union a b empty
-- doubleton could be more efficient

{-| The empty set of disjoint sets. -}
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
        r = M.singleton x 1
    in DisjointSet p r

{-|
Find the set representative for this input. Returns a new disjoint
set in which the path has been compressed.
-}
representative' :: Ord a => a -> DisjointSet a -> (Maybe a, DisjointSet a)
representative' !x set =
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

{- $tutorial

The disjoint set data structure represents sets that are
disjoint. Each set in the data structure can be interpreted
as an equivalance class. For example, let us consider a scenario
in which we are investigating spies who each use one or more aliases. There are three
actions we may repeated take:

    1. we learn an alias is in use by someone (make set)
    2. we learn two aliases refer to the same individual (union)
    3. we check our notes to figure out if two aliases refer to the same individual (find)

We initially learn of the existence of several aliases:

>>> import Data.Function ((&))
>>> import Data.Monoid ((<>))
>>> import Data.Foldable (fold,foldMap)
>>> let s0 = empty
>>> let s1 = s0 & insert "Scar" & insert "Carene" & insert "Barth" & insert "Coral"
>>> let s2 = s1 & insert "Boris" & insert "Esma" & insert "Mayra"
>>> putStr (pretty s2)
{{"Barth"},{"Boris"},{"Carene"},{"Coral"},{"Esma"},{"Mayra"},{"Scar"}}

Note that the 'Monoid' instance gives us a way to construct this more succintly:

>>> s2 == foldMap singleton ["Barth","Boris","Carene","Coral","Esma","Mayra","Scar"]
True

After some preliminary research, we learn that Barth and Esma are the same person. We
also learn that Carene and Mayra are the same:

>>> let s3 = s2 & union "Barth" "Esma" & union "Carene" "Mayra"
>>> putStr (pretty s3)
{{"Boris"},{"Coral"},{"Barth","Esma"},{"Carene","Mayra"},{"Scar"}}

Another informant comes forward who tells us they have worked for someone
that went by the names Mayra and Esma. Going through old letters, we learn
that Boris is a pen name used by Scar:

>>> let s4 = s3 & union "Mayra" "Esma" & union "Boris" "Scar"
>>> putStr (pretty s4)
{{"Coral"},{"Barth","Carene","Esma","Mayra"},{"Boris","Scar"}}

At this point, Detective Laura from another department drops by with
questions about a case she is working on. She asks if Boris the same
person as Barth and if Carene is the same person as Esma. We answer:

>>> equivalent "Boris" "Barth" s4
False
>>> equivalent "Carene" "Esma" s4
True

The correct way to interpret this is that @False@ means something more
along the lines of unknown, but we definitely know that Carene is Esma.
Finally, before the detective leaves, she gives us some of her case
notes to synthesize with our information. Notice that there are
some aliases she encountered that we did not and vice versa:

>>> let laura = union "Scar" "Coral" $ union "Esma" "Henri" $ foldMap singleton ["Carene","Boris","Barth"]
>>> putStr (pretty laura)
{{"Barth"},{"Boris"},{"Carene"},{"Coral","Scar"},{"Esma","Henri"}}
>>> putStr (pretty (laura <> s4))
{{"Barth","Carene","Esma","Henri","Mayra"},{"Boris","Coral","Scar"}}

With Laura's shared findings, we now see that there are really only (at most)
two spies that we are dealing with.

-}

