{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-|
Persistent disjoint-sets. Disjoint-sets are a set of elements 
with equivalence relations defined between elements, i.e. 
two elements may be members of the same equivalence set.
The type in this module can be roughly understood as:

> DisjointSet a ≈ Set (Set a)

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
  , equivalences
  , representative
  , representative'
    -- * Conversion
  , toLists
  , fromLists
  , toSets
  , fromSets
  , pretty
  , showInternal
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
import Data.Foldable (foldlM)
import qualified Data.Semigroup
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L

data DisjointSet a = DisjointSet
  !(Map a a) -- parents
  !(Map a (RankChildren a)) -- ranks

data RankChildren a = RankChildren {-# UNPACK #-} !Int !(Set a)
  deriving Show

data RevealDisjointSet a = RevealDisjointSet
  !(Map a a)
  !(Map a (RankChildren a))
  deriving Show

showInternal :: Show a => DisjointSet a -> String
showInternal (DisjointSet p r) = show (RevealDisjointSet p r)

fromSets :: Ord a => [Set a] -> Maybe (DisjointSet a)
fromSets xs = case unionDistinctAll xs of
  Nothing -> Nothing
  Just _ -> Just (unsafeFromSets xs empty)

unsafeFromSets :: Ord a => [Set a] -> DisjointSet a -> DisjointSet a
unsafeFromSets ys !ds@(DisjointSet p r) = case ys of
  [] -> ds
  x : xs -> case setLookupMin x of
    Nothing -> unsafeFromSets xs ds
    Just m -> unsafeFromSets xs $ DisjointSet
      (M.union (M.fromSet (\_ -> m) x) p)
      (M.insert m (RankChildren 0 x) r)
  

unionDistinctAll :: Ord a => [Set a] -> Maybe (Set a)
unionDistinctAll = foldlM unionDistinct S.empty

unionDistinct :: Ord a => Set a -> Set a -> Maybe (Set a)
unionDistinct a b = 
  let s = S.union a b
   in if S.size a + S.size b == S.size s
        then Just s
        else Nothing

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
showDisjointSet = showString "fromLists " . show . toLists

pretty :: (Ord a, Show a) => DisjointSet a -> String
pretty xs = id
  . showChar '{'
  . applyList (L.intersperse (showChar ',') (map (\x -> showChar '{' . applyList (L.intersperse (showChar ',') (map shows x)) . showChar '}') (toLists xs)))
  . showChar '}'
  $ []

applyList :: [(a -> a)] -> a -> a
applyList [] = id
applyList (f : fs) = f . applyList fs

toLists :: DisjointSet a -> [[a]]
toLists = map S.toList . toSets

-- this definition is pretty awful. Come up with something that
-- behaves a little more reasonably in the presence of failure.
fromLists :: Ord a => [[a]] -> DisjointSet a
fromLists xs = fromMaybe empty (fromSets (map S.fromList xs))

toSets :: DisjointSet a -> [Set a]
toSets (DisjointSet _ r) = M.foldr
  (\(RankChildren _ s) xs -> s : xs) [] r

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
  let RankChildren rankx keysx = r M.! repx
  let RankChildren ranky keysy = r M.! repy
      keys = mappend keysx keysy
  lift $ put $! case compare rankx ranky of
    LT -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (RankChildren ranky keys) r
          in  DisjointSet p' r'
    GT -> let p' = M.insert repy repx p
              r' = M.delete repy $! M.insert repx (RankChildren rankx keys) r
          in  DisjointSet p' r'
    EQ -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (RankChildren (ranky + 1) keys) r
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

{-| All elements the are considered equal to the value. In the event
    that the element does not exist, a singleton set will be returned.
-}
equivalences :: Ord a => a -> DisjointSet a -> Set a
equivalences a (DisjointSet p r) = case M.lookup a p of
  Nothing -> S.singleton a
  Just b -> case M.lookup (lookupUntilRoot b p) r of
    Nothing -> error "Data.DisjointSet equivalences: invariant violated"
    Just (RankChildren _ s) -> s

lookupUntilRoot :: Ord a => a -> Map a a -> a
lookupUntilRoot a m = case M.lookup a m of
  Nothing -> a
  Just a' -> if a == a'
    then a
    else lookupUntilRoot a' m

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
              let r' = M.insert x (RankChildren 0 (S.singleton x)) r
              in  DisjointSet p' r'

{-| Create a disjoint set with one member. O(1). -}
singleton :: a -> DisjointSet a
singleton !x =
  let p = M.singleton x x
      r = M.singleton x (RankChildren 0 (S.singleton x))
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
singletons s = case setLookupMin s of
  Nothing -> empty
  Just x ->
    let p = M.fromSet (\_ -> x) s
        rank = if S.size s == 1 then 0 else 1
        r = M.singleton x (RankChildren rank s)
    in DisjointSet p r

setLookupMin :: Set a -> Maybe a
#if MIN_VERSION_containers(0,5,9) 
setLookupMin = S.lookupMin
#else
setLookupMin s = if S.size s > 0 then Just (S.findMin s) else Nothing
#endif

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

