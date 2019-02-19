{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wall #-}

{-|
Maps with disjoint sets as the key. The type in this module can be
roughly understood as:

> DisjointMap k v ≈ Map (Set k) v

Internally, @DisjointMap@ is implemented like a disjoint set
but the data structure that maps representatives to their rank also holds the value
associated with that representative element. Additionally, it holds the set
of all keys that in the same equivalence class as the representative.
This makes it possible to implementat functions like @foldlWithKeys\'@
efficiently.

-}

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
  , lookup'
  , representative
  , representative'
    -- * Conversion
  , toLists
  , toSets
  , fromSets
  , pretty
  , prettyList
  , foldlWithKeys'
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
import Data.Bifunctor (first)
import Data.Foldable (Foldable)
import Data.Maybe (fromMaybe)
import Data.Aeson (ToJSON(..),FromJSON(..))
import Data.Foldable (foldlM)
import qualified Data.Semigroup as SG
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified GHC.OldList as L

-- | A map having disjoints sets of @k@ as keys and
--   @v@ as values.
data DisjointMap k v = DisjointMap
  !(Map k k) -- parents and values
  !(Map k (Ranked k v)) -- ranks
  deriving (Functor,Foldable,Traversable)

-- the name ranked is no longer totally appropriate since
-- a set of keys has been added in here as well.
data Ranked k v = Ranked {-# UNPACK #-} !Int !(Set k) !v
  deriving (Functor,Foldable,Traversable)

instance (Ord k, Monoid v) => Monoid (DisjointMap k v) where
  mempty = empty

-- | This only satisfies the associativity law when the 'Monoid'
--   instance for @v@ is commutative.
instance (Ord k, Monoid v) => SG.Semigroup (DisjointMap k v) where
  (<>) = append

-- technically, it should be possible to weaken the Ord constraint on v to
-- an Eq constraint
instance (Ord k, Ord v) => Eq (DisjointMap k v) where
  a == b = S.fromList (toSets a) == S.fromList (toSets b)

instance (Ord k, Ord v) => Ord (DisjointMap k v) where
  compare a b = compare (S.fromList (toSets a)) (S.fromList (toSets b))

instance (Show k, Ord k, Show v) => Show (DisjointMap k v) where
  show = showDisjointSet

instance (ToJSON k, ToJSON v) => ToJSON (DisjointMap k v) where
  toJSON = toJSON . toSets

instance (FromJSON k, FromJSON v, Ord k) => FromJSON (DisjointMap k v) where
  parseJSON x = do
    theSets <- parseJSON x
    case fromSets theSets of
      Nothing -> fail "the sets comprising the DisjointSet were not distinct"
      Just s -> return s

fromSets :: Ord k => [(Set k,v)] -> Maybe (DisjointMap k v)
fromSets xs = case unionDistinctAll (map fst xs) of
  Nothing -> Nothing
  Just _ -> Just (unsafeFromSets xs empty)

unsafeFromSets :: Ord k => [(Set k,v)] -> DisjointMap k v -> DisjointMap k v
unsafeFromSets ys !ds@(DisjointMap p r) = case ys of
  [] -> ds
  (x,v) : xs -> case setLookupMin x of
    Nothing -> unsafeFromSets xs ds
    Just m -> unsafeFromSets xs $ DisjointMap
      (M.union (M.fromSet (\_ -> m) x) p)
      (M.insert m (Ranked 0 x v) r)
  

unionDistinctAll :: Ord a => [Set a] -> Maybe (Set a)
unionDistinctAll = foldlM unionDistinct S.empty

unionDistinct :: Ord a => Set a -> Set a -> Maybe (Set a)
unionDistinct a b = 
  let s = S.union a b
   in if S.size a + S.size b == S.size s
        then Just s
        else Nothing

showDisjointSet :: (Show k, Ord k, Show v) => DisjointMap k v -> String
showDisjointSet = show . toLists

toLists :: DisjointMap k v -> [([k],v)]
toLists = (fmap.first) S.toList . toSets

toSets :: DisjointMap k v -> [(Set k,v)]
toSets (DisjointMap _ r) = M.foldr
  (\(Ranked _ s v) xs -> (s,v) : xs) [] r

pretty :: (Show k, Show v) => DisjointMap k v -> String
pretty dm = "{" ++ L.intercalate ", " (prettyList dm) ++ "}"

prettyList :: (Show k, Show v) => DisjointMap k v -> [String]
prettyList dm = L.map (\(ks,v) -> "{" ++ commafied ks ++ "} -> " ++ show v) (toSets dm)

commafied :: Show k => Set k -> String
commafied = join . L.intersperse "," . map show . S.toList

foldlWithKeys' :: (a -> Set k -> v -> a) -> a -> DisjointMap k v -> a
foldlWithKeys' f a0 (DisjointMap _ r) =
  M.foldl' (\a (Ranked _ ks v) -> f a ks v) a0 r

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
  let Ranked rankx keysx valx = r M.! repx
  let Ranked ranky keysy valy = r M.! repy
  let val = mappend valx valy
      keys = mappend keysx keysy
  lift $ put $! case compare rankx ranky of
    LT -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (Ranked ranky keys val) r
          in  DisjointMap p' r'
    GT -> let p' = M.insert repy repx p
              r' = M.delete repy $! M.insert repx (Ranked rankx keys val) r
          in  DisjointMap p' r'
    EQ -> let p' = M.insert repx repy p
              r' = M.delete repx $! M.insert repy (Ranked (ranky + 1) keys val) r
          in  DisjointMap p' r'

{-|
Find the set representative for this input. This function
ignores the values in the map.
-}
representative :: Ord k => k -> DisjointMap k v -> Maybe k
representative = find

{-| Insert a key-value pair into the disjoint map. If the key
    is is already present in another set, combine the value
    monoidally with the value belonging to it. The new value
    is on the left side of the append, and the old value is
    on the right.
    Otherwise, this creates a singleton set as a new key and
    associates it with the value.
-}
insert :: (Ord k, Monoid v) => k -> v -> DisjointMap k v -> DisjointMap k v
insert !x = insertInternal x (S.singleton x)

insertInternal :: (Ord k, Monoid v) => k -> Set k -> v -> DisjointMap k v -> DisjointMap k v
insertInternal !x !ks !v set@(DisjointMap p r) =
  let (l, p') = M.insertLookupWithKey (\_ _ old -> old) x x p
   in case l of
        Just _ ->
          let (m,DisjointMap p2 r') = representative' x set
           in case m of
                Nothing -> error "DisjointMap insert: invariant violated"
                Just root -> DisjointMap p2 (M.adjust (\(Ranked rank oldKs vOld) -> Ranked rank (mappend oldKs ks) (mappend v vOld)) root r')
        Nothing ->
          let r' = M.insert x (Ranked 0 ks v) r
          in  DisjointMap p' r'


{-| Create a disjoint map with one key: a singleton set. O(1). -}
singleton :: k -> v -> DisjointMap k v
singleton !x !v =
  let p = M.singleton x x
      r = M.singleton x (Ranked 0 (S.singleton x) v)
   in DisjointMap p r

{-| The empty map -}
empty :: DisjointMap k v
empty = DisjointMap M.empty M.empty

append :: (Ord k, Monoid v) => DisjointMap k v -> DisjointMap k v -> DisjointMap k v
append s1@(DisjointMap m1 r1) s2@(DisjointMap m2 r2) = if M.size m1 > M.size m2
  then appendParents r2 s1 m2
  else appendParents r1 s2 m1

appendParents :: (Ord k, Monoid v) => Map k (Ranked k v) -> DisjointMap k v -> Map k k -> DisjointMap k v
appendParents !ranks = M.foldlWithKey' $ \ds x y -> if x == y
  then case M.lookup x ranks of
    Nothing -> error "DisjointMap appendParents: invariant violated"
    Just (Ranked _ ks v) -> insertInternal x ks v ds
  else union x y ds

{-| Create a disjoint map with one key. Everything in the
    'Set' argument is consider part of the same equivalence
    class.
-}
singletons :: Eq k => Set k -> v -> DisjointMap k v
singletons s v = case setLookupMin s of
  Nothing -> empty
  Just x ->
    let p = M.fromSet (\_ -> x) s
        rank = if S.size s == 1 then 0 else 1
        r = M.singleton x (Ranked rank s v)
    in DisjointMap p r

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
    the provided key. If the key is not found, use 'mempty'.
-}
lookup :: (Ord k, Monoid v) => k -> DisjointMap k v -> v
lookup k = fromMaybe mempty . lookup' k

{-| Find the value associated with the set containing
    the provided key.
-}
lookup' :: Ord k => k -> DisjointMap k v -> Maybe v
lookup' !x (DisjointMap p r) =
  do x' <- M.lookup x p
     if x == x'
       then case M.lookup x r of
         Nothing -> Nothing
         Just (Ranked _ _ v) -> Just v
       else find' x'
  where find' y = let y' = p M.! y
                   in if y == y'
                        then case M.lookup y r of
                          Nothing -> Nothing
                          Just (Ranked _ _ v) -> Just v
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

{- $tutorial

The disjoint map data structure can be used to model scenarios where
the key of a map is a disjoint set. Let us consider trying to find
the lowest rating of our by town. Due to differing subcultures,
inhabitants do not necessarily agree on a canonical name for each town.
Consequently, the survey allows participants to write in their town
name as they would call it. We begin with a rating data type:

>>> import Data.Function ((&))
>>> data Rating = Lowest | Low | Medium | High | Highest deriving (Eq,Ord,Show)
>>> instance Monoid Rating where mempty = Highest; mappend = min

Notice that the 'Monoid' instance combines ratings by choosing
the lower one. Now, we consider the data from the survey:

>>> let resA = [("Big Lake",High),("Newport Lake",Medium),("Dustboro",Low)]
>>> let resB = [("Sand Town",Medium),("Sand Town",High),("Mount Lucy",High)]
>>> let resC = [("Lucy Hill",Highest),("Dustboro",High),("Dustville",High)]
>>> let m1 = foldMap (uncurry singleton) (resA ++ resB ++ resC)
>>> :t m1
m1 :: DisjointMap [Char] Rating
>>> mapM_ putStrLn (prettyList m1)
{"Big Lake"} -> High
{"Dustboro"} -> Low
{"Dustville"} -> High
{"Lucy Hill"} -> Highest
{"Mount Lucy"} -> High
{"Newport Lake"} -> Medium
{"Sand Town"} -> Medium

Since we haven't defined any equivalence classes for the town names yet,
what we have so far is no different from an ordinary 'Map'. Now we
will introduce some equivalences:

>>> let m2 = m1 & union "Big Lake" "Newport Lake" & union "Sand Town" "Dustboro"
>>> let m3 = m2 & union "Dustboro" "Dustville" & union "Lucy Hill" "Mount Lucy"
>>> mapM_ putStrLn (prettyList m3)
{"Dustboro","Dustville","Sand Town"} -> Low
{"Lucy Hill","Mount Lucy"} -> High
{"Big Lake","Newport Lake"} -> Medium

We can now query the map to find the lowest rating in a given town:

>>> lookup "Dustville" m3
Low
>>> lookup "Lucy Hill" m3
High

-}

