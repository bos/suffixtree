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
-- The implementation is based on the first one described in the
-- following paper:
-- 
--   * Robert Giegerich and Stefan Kurtz, \"/A comparison of
--     imperative and purely functional suffix tree constructions/\",
--     Science of Computer Programming 25(2-3):187-218, 1995,
--     <http://citeseer.ist.psu.edu/giegerich95comparison.html>

module Data.SuffixTree
    ( Edge
    , Length
    , STree(..)
    , constructWith
    , construct
    , elem
    , fold
    , length
    , suffixes
    , take
    ) where
                   
import Prelude hiding (elem, length, take)
import qualified Data.Map as M
import Data.List (foldl')
import Control.Arrow (second)
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import qualified Data.List as L

data Length a = Exactly {-# UNPACK #-} !Int
              | Sum {-# UNPACK #-} !Int [a]
              deriving (Show)

length :: Length a -> Int
length (Exactly n) = n
length (Sum n xs) = n + L.length xs

inc :: Length a -> Length a
inc (Exactly n) = Exactly (n+1)
inc (Sum n xs)  = Sum (n+1) xs

take :: Length a -> [a] -> [a]
take (Exactly n) = L.take n
take (Sum n xs) = tk n
    where tk 0 ys = zipWith (const id) xs ys
          tk n (y:ys) = y : tk (n-1) ys

type Edge a = ([a], Length a)

type EdgeFunction a = [[a]] -> (Length a, [[a]])

data STree a = Node [(Edge a, STree a)]
             | Leaf
               deriving (Show)

fold :: ([a] -> b -> b) -> b -> STree a -> b
fold _ z Leaf = z
fold f z (Node es) = foldr (\ ((l, n), t) v -> f (take n l) (fold f v t)) z es

lazyTreeWith :: (Eq a) => EdgeFunction a -> [a] -> [a] -> STree a
lazyTreeWith edge alphabet = suf . suffixes
    where suf [[]] = Leaf
          suf ss = Node [((a:sa, inc cpl), suf ssr)
                         | a <- alphabet,
                           n@(sa:_) <- [ss `clusterBy` a],
                           (cpl,ssr) <- [edge n]]
          clusterBy ss a = [cs | c:cs <- ss, c == a]

suffixes :: [a] -> [[a]]
suffixes xs@(_:xs') = xs : suffixes xs'
suffixes _ = []

lazyTree :: (Ord a) => EdgeFunction a -> [a] -> STree a
lazyTree edge = suf . suffixes
    where suf [[]] = Leaf
          suf ss = Node [((a:sa, inc cpl), suf ssr)
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
                                     in cpl' `seq` (cpl', rss)
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
constructWith :: (Eq a) => [a] -> [a] -> STree a
constructWith = lazyTreeWith cst

{-# SPECIALISE construct :: [Char] -> STree Char #-}
{-# SPECIALISE construct :: [[Char]] -> STree [Char] #-}
{-# SPECIALISE construct :: [SB.ByteString] -> STree SB.ByteString #-}
{-# SPECIALISE construct :: [LB.ByteString] -> STree LB.ByteString #-}
{-# SPECIALISE construct :: (Ord a) => [[a]] -> STree [a] #-}
construct :: (Ord a) => [a] -> STree a
construct = lazyTree cst

{-# SPECIALISE elem :: [Char] -> STree Char -> Bool #-}
{-# SPECIALISE elem :: [[Char]] -> STree [Char] -> Bool #-}
{-# SPECIALISE elem :: [SB.ByteString] -> STree SB.ByteString -> Bool #-}
{-# SPECIALISE elem :: [LB.ByteString] -> STree LB.ByteString -> Bool #-}
{-# SPECIALISE elem :: (Eq a) => [[a]] -> STree [a] -> Bool #-}
elem :: (Eq a) => [a] -> STree a -> Bool
elem [] _ = True
elem _ Leaf = False
elem xs (Node es) = any prefix es
    where prefix ((l, n), t) = maybe False (`elem` t) (rsuf (take n l) xs)
          rsuf (l:ls) (x:xs) | l == x = rsuf ls xs
                             | otherwise = Nothing
          rsuf _ xs = Just xs
