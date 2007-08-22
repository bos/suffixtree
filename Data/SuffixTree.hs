{- Fastest when compiled as follows: ghc -O2 -optc-O3 -funbox-strict-fields -}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.SuffixTree
-- Copyright   :  (c) Bryan O'Sullivan 2007
-- License     :  BSD-style
-- Maintainer  :  bos@serpentine.com
-- Stability   :  experimental
-- Portability :  portable
--
-- A lazy, efficient suffix tree implementation.
--
-- Since many function names (but not the type name) clash with
-- "Prelude" names, this module is usually imported @qualified@, e.g.
--
-- >  import Data.SuffixTree (STree)
-- >  import qualified Data.SuffixTree as T
--
-- The implementation is based on the first of those described in the
-- following paper:
-- 
--   * Robert Giegerich and Stefan Kurtz, \"/A comparison of
--     imperative and purely functional suffix tree constructions/\",
--     Science of Computer Programming 25(2-3):187-218, 1995,
--     <http://citeseer.ist.psu.edu/giegerich95comparison.html>
-- 
-- This implementation constructs the suffix tree lazily, so subtrees
-- are not created until they are traversed.  Two construction
-- functions are provided, 'constructWith' for sequences composed of
-- small alphabets, and 'construct' for larger alphabets.

module Data.SuffixTree
    (
    -- * Types
      Alphabet
    , Prefix
    , STree(..)

    -- * Construction
    , constructWith
    , construct

    -- * Querying
    , elem
    , find

    -- * Traversal
    , fold
    , fold'

    -- * Other useful functions
    , prefix
    , suffixes
    ) where
                   
import Prelude hiding (elem)
import qualified Data.Map as M
import Data.List (foldl')
import Control.Arrow (second)
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import Data.Maybe (listToMaybe, mapMaybe)

-- | The length of a prefix list.  This type is formulated to do cheap
-- work eagerly (to avoid constructing a pile of deferred thunks),
-- while deferring potentially expensive work.
data Length a = Exactly {-# UNPACK #-} !Int
              | Sum {-# UNPACK #-} !Int [a]
              deriving (Show)

-- | The list of symbols that 'constructWith' can possibly see in its
-- input.
type Alphabet a = [a]

-- | The prefix string associated with an 'Edge'.
newtype Prefix a = Prefix ([a], Length a)
    deriving (Show)

instance (Eq a) => Eq (Prefix a) where
    a == b = prefix a == prefix b

type EdgeFunction a = [[a]] -> (Length a, [[a]])

-- | A suffix tree.  The implementation is exposed to ease the
-- development of custom traversal functions.  Note that @('Prefix' a,
-- 'STree' a)@ pairs are not stored in any order.
data STree a = Node [(Prefix a, STree a)]
             | Leaf
               deriving (Show)

-- | Obtain the list stored in a 'Prefix'.
prefix :: Prefix a -> [a]
prefix (Prefix (ys, Exactly n)) = take n ys
prefix (Prefix (ys, Sum n xs)) = tk n ys
    where tk 0 ys = zipWith (const id) xs ys
          tk n (y:ys) = y : tk (n-1) ys

-- | /O(n)/. Fold the edges in a tree, from bottom to top.  Suitable
-- for lazy use.
fold :: (Prefix a -> b -> b) -> b -> STree a -> b
fold _ z Leaf = z
fold f z (Node es) = foldr (\(e, t) v -> f e (fold f v t)) z es

-- | /O(n)/. Fold the edges in a tree, from bottom to top.  Suitable
-- for strict use.
fold' :: (a -> Prefix b -> a) -> a -> STree b -> a
fold' _ z Leaf = z
fold' f z (Node es) = foldl' (\v (e, t) -> f (fold' f v t) e) z es

-- | Increment the length of a prefix.
inc :: Length a -> Length a
inc (Exactly n) = Exactly (n+1)
inc (Sum n xs)  = Sum (n+1) xs

lazyTreeWith :: (Eq a) => EdgeFunction a -> Alphabet a -> [a] -> STree a
lazyTreeWith edge alphabet = suf . suffixes
    where suf [[]] = Leaf
          suf ss = Node [(Prefix (a:sa, inc cpl), suf ssr)
                         | a <- alphabet,
                           n@(sa:_) <- [ss `clusterBy` a],
                           (cpl,ssr) <- [edge n]]
          clusterBy ss a = [cs | c:cs <- ss, c == a]

-- | Return all non-empty suffixes of the argument, longest first.
-- Behaves as follows:
--
-- >suffixes xs == init (tails xs)
suffixes :: [a] -> [[a]]
suffixes xs@(_:xs') = xs : suffixes xs'
suffixes _ = []

lazyTree :: (Ord a) => EdgeFunction a -> [a] -> STree a
lazyTree edge = suf . suffixes
    where suf [[]] = Leaf
          suf ss = Node [(Prefix (a:sa, inc cpl), suf ssr)
                         | (a, n@(sa:_)) <- suffixMap ss,
                           (cpl,ssr) <- [edge n]]

suffixMap :: Ord a => [[a]] -> [(a, [[a]])]
suffixMap = map (second reverse) . M.toList . foldl' step M.empty
    where step m (x:xs) = M.alter (f xs) x m
          step m _ = m
          f x Nothing = Just [x]
          f x (Just xs) = Just (x:xs)

cst :: Eq a => EdgeFunction a
cst [s] = (Sum 0 s, [[]])
cst awss@((a:w):ss)
    | null [c | c:_ <- ss, a /= c] = let cpl' = inc cpl
                                     in seq cpl' (cpl', rss)
    | otherwise = (Exactly 0, awss)
    where (cpl, rss) = cst (w:[u | _:u <- ss])

pst :: Eq a => EdgeFunction a
pst = g . dropNested
    where g [s] = (Sum 0 s, [[]])
          g ss  = (Exactly 0, ss)
          dropNested ss@[_] = ss
          dropNested awss@((a:w):ss)
              | null [c | c:_ <- ss, a /= c] = [a:s | s <- rss]
              | otherwise = awss
              where rss = dropNested (w:[u | _:u <- ss])

{-# SPECIALISE constructWith :: [Char] -> [Char] -> STree Char #-}
{-# SPECIALISE constructWith :: [[Char]] -> [[Char]] -> STree [Char] #-}
{-# SPECIALISE constructWith :: [SB.ByteString] -> [SB.ByteString]
                             -> STree SB.ByteString #-}
{-# SPECIALISE constructWith :: [LB.ByteString] -> [LB.ByteString]
                             -> STree LB.ByteString #-}
{-# SPECIALISE constructWith :: (Eq a) => [[a]] -> [[a]] -> STree [a] #-}

-- | /O(k n log n)/.  Construct a suffix tree using the given
-- alphabet.  The performance of this function is linear in the size
-- /k/ of the alphabet.  That makes this function suitable for small
-- alphabets, such as DNA nucleotides.  For an alphabet containing
-- more than a few symbols, 'construct' is usually several orders of
-- magnitude faster.
constructWith :: (Eq a) => Alphabet a -> [a] -> STree a
constructWith = lazyTreeWith cst

{-# SPECIALISE construct :: [Char] -> STree Char #-}
{-# SPECIALISE construct :: [[Char]] -> STree [Char] #-}
{-# SPECIALISE construct :: [SB.ByteString] -> STree SB.ByteString #-}
{-# SPECIALISE construct :: [LB.ByteString] -> STree LB.ByteString #-}
{-# SPECIALISE construct :: (Ord a) => [[a]] -> STree [a] #-}

-- | /O(n log n)/.  Construct a suffix tree.
construct :: (Ord a) => [a] -> STree a
construct = lazyTree cst

suffix :: (Eq a) => [a] -> [a] -> Maybe [a]
suffix (l:ls) (x:xs) | l == x = suffix ls xs
                     | otherwise = Nothing
suffix _ xs = Just xs

{-# SPECIALISE elem :: [Char] -> STree Char -> Bool #-}
{-# SPECIALISE elem :: [[Char]] -> STree [Char] -> Bool #-}
{-# SPECIALISE elem :: [SB.ByteString] -> STree SB.ByteString -> Bool #-}
{-# SPECIALISE elem :: [LB.ByteString] -> STree LB.ByteString -> Bool #-}
{-# SPECIALISE elem :: (Eq a) => [[a]] -> STree [a] -> Bool #-}

-- | /O(n)/.  Indicate the suffix tree contains the given subsequence.
-- Performance is linear in the length of the subsequence.
elem :: (Eq a) => [a] -> STree a -> Bool
elem [] _ = True
elem _ Leaf = False
elem xs (Node es) = any pfx es
    where pfx (e, t) = maybe False (`elem` t) (suffix (prefix e) xs)

{-# SPECIALISE find :: [Char] -> STree Char
                    -> Maybe (Prefix Char, STree Char) #-}
{-# SPECIALISE find :: [[Char]] -> STree [Char]
                    -> Maybe (Prefix [Char], STree [Char]) #-}
{-# SPECIALISE find :: [SB.ByteString] -> STree SB.ByteString
                    -> Maybe (Prefix SB.ByteString, STree SB.ByteString) #-}
{-# SPECIALISE find :: [LB.ByteString] -> STree LB.ByteString
                    -> Maybe (Prefix LB.ByteString, STree LB.ByteString) #-}
{-# SPECIALISE find :: (Eq a) => [[a]] -> STree [a]
                    -> Maybe (Prefix [a], STree [a]) #-}

-- | /O(n)/.  Return the portion of the suffix tree at which the given
-- subsequence is located.  If the subsequence is not found, return
-- 'Nothing'.
find :: (Eq a) => [a] -> STree a -> Maybe (Prefix a, STree a)
find _ Leaf = Nothing
find xs (Node es) = listToMaybe (mapMaybe pfx es)
    where pfx p@(e, t) = suffix (prefix e) xs >>= \suf ->
            case suf of
              [] -> return p
              s -> find s t
