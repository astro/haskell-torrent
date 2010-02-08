module SparseMap (SparseMap,
                  empty,
                  toList,
                  fromList,
                  insert,
                  lookup,
                  delete,
                  alter,
                  adjust,
                  keys,
                  all,
                  filter) where
-- ^ Layer on top of Data.Map for dictionaries with a contiguous set
--   of keys and many recurring values. SparseMap saves space and time
--   by storing ranges of adjacent keys with the same value. This buys
--   very small memory usage for storing maps like PieceDoneMaps.

import Data.List (foldl')
import qualified Data.Map as Map
import Prelude hiding (lookup, all, filter)
import qualified Prelude


-- |Just wrap the map
newtype SparseMap k a = SM { smInner :: (Map.Map (k, k) a) }
    deriving (Show, Eq)

empty = SM Map.empty

toList :: Enum k => SparseMap k a -> [(k, a)]
toList = concatMap (\((k, k'), a) ->
                        zip [k..k'] $ repeat a
                   ) .
         Map.toList .
         smInner

fromList :: (Ord k, Enum k, Eq a) => [(k, a)] -> SparseMap k a
fromList = foldl' (\sm (k, a) ->
                       insert k a sm
                  ) empty

-- | Merges adjacent ranges with equal values. Repeats until
--   neighboring keys are not equal anymore.
optimize :: (Enum k, Ord k, Eq a) => (k, k) -> SparseMap k a -> SparseMap k a
optimize (k, k') sm@(SM inner) = case Map.splitLookup (k, k') inner of
                                   (less, Just a, _)
                                       | not (Map.null less) &&
                                         succ prevK' == k &&
                                         prevA == a ->
                                             --trace ("optimizing " ++ show (prevK, prevK') ++ " with " ++ show (k, k')) $
                                             optimize (prevK, k') $
                                             insertRange (prevK, k') a $
                                             SM $
                                             Map.delete (prevK, prevK') $
                                             Map.delete (k, k') $
                                             inner
                                       where ((prevK, prevK'), prevA) = Map.findMax less
                                   (_, Just a, greater)
                                       | not (Map.null greater) &&
                                         pred nextK == k' &&
                                         nextA == a ->
                                             --trace ("optimizing " ++ show (nextK, nextK') ++ " with " ++ show (k, k')) $
                                             optimize (k, nextK') $
                                             insertRange (k, nextK') a $
                                             SM $
                                             Map.delete (nextK, nextK') $
                                             Map.delete (k, k') $
                                             inner
                                       where ((nextK, nextK'), nextA) = Map.findMin greater
                                   _ ->
                                       sm



insertRange :: Ord k => (k, k) -> a -> SparseMap k a -> SparseMap k a
insertRange (k, k') a | k > k' = id
insertRange k a = SM . Map.insert k a . smInner

insertRanges :: (Ord k, Enum k, Eq k, Eq a) => [((k, k), a)] -> SparseMap k a -> SparseMap k a
insertRanges [] = id
-- | Drop when range is negative
insertRanges (((k, k'), a) : ranges)
    | k > k' =
        insertRanges ranges
-- | Merge equivalent neighboring ranges
insertRanges (((k1, k1'), a1) : ((k2, k2'), a2) : ranges)
    | succ k1' == k2 && a1 == a2 =
        insertRanges (((k1, k2'), a1) : ranges)
-- | Insert ranges
insertRanges ((k, a) : ranges) =
    insertRanges ranges .
    insertRange k a

insert :: (Ord k, Enum k, Eq a) => k -> a -> SparseMap k a -> SparseMap k a
insert k a sm@(SM inner) =
    case lookupRange k sm of
      Just (oldRange, old) ->
          let new = [((fst oldRange, pred k), old),
                     ((k, k), a),
                     ((succ k, snd oldRange), old)]
              inner' = SM $ Map.delete oldRange inner
              inner'' | a == old = sm  -- ^No change
                      | otherwise = insertRanges new inner'
          in optimize (k, k) inner''
      Nothing ->
          optimize (k, k) $
          insertRange (k, k) a sm

-- | Very important: which present range includes k?
lookupRange :: Ord k => k -> SparseMap k a -> Maybe ((k, k), a)
lookupRange k (SM inner) =
    case Map.splitLookup (k, k) inner of
      (_, Just a, _) ->
          Just ((k, k), a)
      (less, Nothing, _)
          | not (Map.null less) &&
            fst prev `inRange` k ->
              Just prev
          where prev = Map.findMax less
      (_, Nothing, greater)
          | not (Map.null greater) &&
            fst next `inRange` k ->
              Just next
          where next = Map.findMin greater
      _ ->
          Nothing
    where -- | Data.Ix.inRange wants Ix instances but Ord is much more
          --   common here
          inRange (k, k') t = k <= t && t <= k'


lookup :: Ord k => k -> SparseMap k a -> Maybe a
lookup k sm =
    do (_, a) <- lookupRange k sm
       return a

delete k sm@(SM inner) =
    case lookupRange k sm of
      Just (oldRange, old) ->
          let new = [((fst oldRange, pred k), old),
                     ((succ k, snd oldRange), old)]
              inner' = SM $ Map.delete oldRange inner
              inner'' = insertRanges new inner'
          in inner''
      Nothing ->
          sm

alter :: (Ord k, Enum k, Eq a) =>
         (Maybe a -> Maybe a) -> k -> SparseMap k a -> SparseMap k a
alter f k sm = let mbA = lookup k sm
                   mbA' = f mbA
               in case (mbA, mbA') of
                    (Nothing, Nothing) ->
                        sm
                    (Just _, Nothing) ->
                        delete k sm
                    (_, Just a) ->
                        insert k a sm

adjust :: (Ord k, Enum k, Eq a) =>
          (a -> a) -> k -> SparseMap k a -> SparseMap k a
adjust f = alter (>>= return . f)

keys :: Enum k => SparseMap k a -> [k]
keys = concatMap (\(k, k') -> [k..k']) .
       Map.keys .
       smInner

all :: (a -> Bool) -> SparseMap k a -> Bool
all f = Map.fold (\a ->
                      (&& f a)
                 ) True .
        smInner

filter :: Ord k => (a -> Bool) -> SparseMap k a -> SparseMap k a
filter f = SM . Map.filter f . smInner

{-
instance F.Foldable (SparseMap k) where
    foldr :: (a -> b -> b) -> b -> t a -> b
    foldr = Map.foldrWithKey  :: (k -> a -> b -> b) -> b -> Map  k a -> b
    foldMap f = foldWithKey (\(k, k') a b ->
                                 foldl' (\b k ->
                                             b `mappend` f a
                                        ) b [k..k']
                            ) mempty

foldWithKey  :: (k -> a -> b -> b) -> b -> Map  k a -> b
-}

prop_Identity :: [Bool] -> Bool
prop_Identity bools = let contents = zip [1..] bools
                      in contents == toList (fromList contents)

prop_Behavior :: [Int] -> Bool
prop_Behavior ints = runUp Map.empty empty ints'
    where ints' = map (`mod` 10) ints
          runUp :: (Map.Map Int ()) -> (SparseMap Int ()) -> [Int] -> Bool
          runUp m sm [] = runDown m sm ints'
          runUp m sm (i:is) = let m' = Map.insert i () m
                                  sm' = insert i () sm
                              in Map.toList m' == toList sm' &&
                                 runUp m' sm' is
          runDown :: (Map.Map Int ()) -> (SparseMap Int ()) -> [Int] -> Bool
          runDown m sm [] = True
          runDown m sm (i:is) = let m' = Map.delete i m
                                    sm' = delete i sm
                                in Map.toList m' == toList sm' &&
                                   runDown m' sm' is
