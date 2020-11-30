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
--
-- Estimates are given for performance.  The value /k/ is a constant;
-- /n/ is the length of a query string; and /t/ is the number of
-- elements (nodes and leaves) in a suffix tree.

module Data.SuffixTree
    (
    -- * Types
      Alphabet
    , Edge
    , Prefix
    , STree(..)

    -- * Construction
    , constructWith
    , construct

    -- * Querying
    , elem
    , findEdge
    , findTree
    , findPath
    , countLeaves
    , countRepeats

    -- * Traversal
    , foldr
    , foldl
    , fold

    -- * Other useful functions
    , mkPrefix
    , prefix
    , suffixes
    ) where
                   
import Prelude hiding (elem, foldl, foldr)
import qualified Data.Map as M
import Data.Either (rights)
import Control.Arrow (second)
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import qualified Data.List as L
import Data.Maybe (listToMaybe, mapMaybe)

-- | The length of a prefix list.  This type is formulated to do cheap
-- work eagerly (to avoid constructing a pile of deferred thunks),
-- while deferring potentially expensive work (computing the length of
-- a list).
data Length a = Exactly {-# UNPACK #-} !Int
              | Sum {-# UNPACK #-} !Int [a]
              deriving (Show)

-- | The list of symbols that 'constructWith' can possibly see in its
-- input.
type Alphabet a = [a]

-- | The prefix string associated with an 'Edge'.  Use 'mkPrefix' to
-- create a value of this type, and 'prefix' to deconstruct one.
newtype Prefix a = Prefix ([a], Length a)

instance (Eq a) => Eq (Prefix a) where
    a == b = prefix a == prefix b

instance (Ord a) => Ord (Prefix a) where
    compare a b = compare (prefix a) (prefix b)

instance (Show a) => Show (Prefix a) where
    show a = "mkPrefix " ++ show (prefix a)

type EdgeFunction a = [Suffix a] -> (Length a, [Suffix a])

type Suffix a = ([a], LeafValue)

type LeafValue = (Int, Int)
-- | An edge in the suffix tree.
type Edge a = (Prefix a, STree a)

-- | /O(1)/. Construct a 'Prefix' value.
mkPrefix :: [a] -> Prefix a
mkPrefix xs = Prefix (xs, Sum 0 xs)

pmap :: (a -> b) -> Prefix a -> Prefix b
pmap f = mkPrefix . map f . prefix

instance Functor Prefix where
    fmap = pmap

-- | The suffix tree type.  The implementation is exposed to ease the
-- development of custom traversal functions.  Note that @('Prefix' a,
-- 'STree' a)@ pairs are not stored in any order.
data STree a = Node [Edge a]
             | Leaf LeafValue
               deriving (Show)

smap :: (a -> b) -> STree a -> STree b
smap _ (Leaf n) = Leaf n
smap f (Node es) = Node (map (\(p, t) -> (fmap f p, smap f t)) es)

instance Functor STree where
    fmap = smap

-- | /O(n)/. Obtain the list stored in a 'Prefix'.
prefix :: Prefix a -> [a]
prefix (Prefix (ys, Exactly n)) = take n ys
prefix (Prefix (ys, Sum n xs)) = tk n ys
    where tk 0 ys = zipWith (const id) xs ys
          tk n (y:ys) = y : tk (n-1) ys

-- | /O(t)/. Folds the edges in a tree, using post-order traversal.
-- Suitable for lazy use.
foldr :: (Prefix a -> b -> b) -> b -> STree a -> b
foldr _ z (Leaf n) = z
foldr f z (Node es) = L.foldr (\(p,t) v -> f p (foldr f v t)) z es

-- | /O(t)/. Folds the edges in a tree, using pre-order traversal.  The
-- step function is evaluated strictly.
foldl :: (a -> Prefix b -> a)   -- ^ step function (evaluated strictly)
      -> a                      -- ^ initial state
      -> STree b
      -> a
foldl _ z (Leaf n) = z
foldl f z (Node es) = L.foldl' (\v (p,t) -> f (foldl f v t) p) z es

-- | /O(t)/. Generic fold over a tree.
--
-- A few simple examples.
--
-- >countLeaves == fold id id (const const) (1+) 0
--
-- >countEdges = fold id id (\_ a _ -> a+1) id 0
--
-- This more complicated example generates a tree of the same shape,
-- but new type, with annotated leaves.
--
-- @
--data GenTree a b = GenNode [('Prefix' a, GenTree a b)]
--                 | GenLeaf b
--                   deriving ('Show')
-- @
-- 
-- @
--gentree :: 'STree' a -> GenTree a Int
--gentree = 'fold' reset id fprefix reset leaf
--    where leaf = GenLeaf 1
--          reset = 'const' leaf
--          fprefix p t (GenLeaf _) = GenNode [(p, t)]
--          fprefix p t (GenNode es) = GenNode ((p, t):es)
-- @
fold :: (a -> a)                -- ^ downwards state transformer
     -> (a -> a)                -- ^ upwards state transformer
     -> (Prefix b -> a -> a -> a) -- ^ edge state transformer
     -> (a -> LeafValue -> a)                -- ^ leaf state transformer
     -> a                       -- ^ initial state
     -> STree b                 -- ^ tree
     -> a
fold fdown fup fprefix fleaf = go
    where go v (Leaf n) = fleaf v n
          go v (Node es) = fup (L.foldr edge v es)
          edge (p, t) v = fprefix p (go (fdown v) t) v

-- | Increments the length of a prefix.
inc :: Length a -> Length a
inc (Exactly n) = Exactly (n+1)
inc (Sum n xs)  = Sum (n+1) xs

removeEithers :: STree (Either Int a) -> STree a
removeEithers (Leaf l) = Leaf l
removeEithers (Node es) = Node $ map (\(p, t) -> (f p, removeEithers t)) es
    where f = mkPrefix . rights . prefix

terminatedSuffixes :: Int -> [a] -> [Suffix (Either Int a)]
terminatedSuffixes n xs = zip (init . init . L.tails $ rs) ps
    where ps = map (\i -> (n, i)) ([0..] :: [Int])
          rs = map Right xs ++ [Left n]

lazyTreeWith :: (Eq a) => EdgeFunction (Either Int a) -> Alphabet a -> [[a]] -> STree a
lazyTreeWith edge alphabet xss = removeEithers . suf . concat . (zipWith terminatedSuffixes [0..]) $ xss
    where alphabet' = map Right alphabet ++ (map Left [0..(length xss - 1)])
          suf [([], j)] = (Leaf j)
          suf ss = Node [(Prefix (a:sa, inc cpl), suf ssr)
                         | a <- alphabet',
                           n@((sa,j):_) <- [ss `clusterBy` a],
                           (cpl,ssr) <- [edge n]]
          clusterBy ss a = [(cs,j) | (c:cs,j) <- ss, c == a]

-- | /O(n)/. Returns all non-empty suffixes of the argument, longest
-- first.  Behaves as follows:
--
-- >suffixes xs == init (tails xs)
suffixes :: [a] -> [[a]]
suffixes xs@(_:xs') = xs : suffixes xs'
suffixes _ = []

lazyTree :: (Ord a) => EdgeFunction (Either Int a) -> [[a]] -> STree a
lazyTree edge = removeEithers . suf . concat . (zipWith terminatedSuffixes [0..])
    where suf [([], j)] = Leaf j
          suf ss = Node [(Prefix (a:sa, inc cpl), suf ssr)
                         | (a, n@((sa, j):_)) <- suffixMap ss,
                           (cpl,ssr) <- [edge n]]

suffixMap :: Ord a => [Suffix a] -> [(a, [Suffix a])]
suffixMap =  map (second reverse) . M.toList . L.foldl' step M.empty
    where step :: Ord a => M.Map a [Suffix a] -> Suffix a -> M.Map a [Suffix a] 
          step m (x:xs,j) = M.alter (f j xs) x m
          step m _ = m
          f j x Nothing = Just [(x, j)]
          f j x (Just xs) = Just ((x,j):xs)

cst :: Eq a => EdgeFunction a
cst [(s, j)] = (Sum 0 s, [([], j)])
cst awss@((a:w,j):ss)
    | null [c | (c:_,_) <- ss, a /= c] = let cpl' = inc cpl
                                         in seq cpl' (cpl', rss)
    | otherwise = (Exactly 0, awss)
    where (cpl, rss) = cst ((w,j):[(u,j') | (_:u,j') <- ss])

pst :: Eq a => EdgeFunction a
pst = g . dropNested
    where g [(s,j)] = (Sum 0 s, [([], j)])
          g ss  = (Exactly 0, ss)
          dropNested ss@[_] = ss
          dropNested awss@((a:w,j):ss)
              | null [c | ((c:_),_) <- ss, a /= c] = [(a:s,j') | (s,j') <- rss]
              | otherwise = awss
              where rss = dropNested ((w,j):[(u,j') | (_:u,j') <- ss])

{-# SPECIALISE constructWith :: [Char] -> [Char] -> STree Char #-}
{-# SPECIALISE constructWith :: [[Char]] -> [[Char]] -> STree [Char] #-}
{-# SPECIALISE constructWith :: [SB.ByteString] -> [SB.ByteString]
                             -> STree SB.ByteString #-}
{-# SPECIALISE constructWith :: [LB.ByteString] -> [LB.ByteString]
                             -> STree LB.ByteString #-}
{-# SPECIALISE constructWith :: (Eq a) => [[a]] -> [[a]] -> STree [a] #-}

-- | /O(k n log n)/.  Constructs a suffix tree using the given
-- alphabet.  The performance of this function is linear in the size
-- /k/ of the alphabet.  That makes this function suitable for small
-- alphabets, such as DNA nucleotides.  For an alphabet containing
-- more than a few symbols, 'construct' is usually several orders of
-- magnitude faster.
constructWith :: (Eq a) => Alphabet a -> [a] -> STree a
constructWith alphabet xs = lazyTreeWith cst alphabet [xs]

constructGeneralWith :: (Eq a) => Alphabet a -> [[a]] -> STree a
constructGeneralWith = lazyTreeWith cst

{-# SPECIALISE construct :: [Char] -> STree Char #-}
{-# SPECIALISE construct :: [[Char]] -> STree [Char] #-}
{-# SPECIALISE construct :: [SB.ByteString] -> STree SB.ByteString #-}
{-# SPECIALISE construct :: [LB.ByteString] -> STree LB.ByteString #-}
{-# SPECIALISE construct :: (Ord a) => [[a]] -> STree [a] #-}

-- | /O(n log n)/.  Constructs a suffix tree.
construct :: (Ord a) => [a] -> STree a
construct xs = lazyTree cst [xs]

constructGeneral :: (Ord a) => [[a]] -> STree a
constructGeneral = lazyTree cst

suffix :: (Eq a) => [a] -> [a] -> Maybe [a]
suffix (p:ps) (x:xs) | p == x = suffix ps xs
                     | otherwise = Nothing
suffix _ xs = Just xs

{-# SPECIALISE elem :: [Char] -> STree Char -> Bool #-}
{-# SPECIALISE elem :: [[Char]] -> STree [Char] -> Bool #-}
{-# SPECIALISE elem :: [SB.ByteString] -> STree SB.ByteString -> Bool #-}
{-# SPECIALISE elem :: [LB.ByteString] -> STree LB.ByteString -> Bool #-}
{-# SPECIALISE elem :: (Eq a) => [[a]] -> STree [a] -> Bool #-}

-- | /O(n)/.  Indicates whether the suffix tree contains the given
-- sublist.  Performance is linear in the length /n/ of the
-- sublist.
elem :: (Eq a) => [a] -> STree a -> Bool
elem [] _ = True
elem _ (Leaf _) = False
elem xs (Node es) = any pfx es
    where pfx (e, t) = maybe False (`elem` t) (suffix (prefix e) xs)

{-# SPECIALISE findEdge :: [Char] -> STree Char
                        -> Maybe (Edge Char, Int) #-}
{-# SPECIALISE findEdge :: [String] -> STree String
                        -> Maybe (Edge String, Int) #-}
{-# SPECIALISE findEdge :: [SB.ByteString] -> STree SB.ByteString
                        -> Maybe (Edge SB.ByteString, Int) #-}
{-# SPECIALISE findEdge :: [ LB.ByteString] -> STree LB.ByteString
                        -> Maybe (Edge LB.ByteString, Int) #-}
{-# SPECIALISE findEdge :: (Eq a) => [[a]] -> STree [a]
                        -> Maybe (Edge [a], Int) #-}

-- | /O(n)/.  Finds the given subsequence in the suffix tree.  On
-- failure, returns 'Nothing'.  On success, returns the 'Edge' in the
-- suffix tree at which the subsequence ends, along with the number of
-- elements to drop from the prefix of the 'Edge' to get the \"real\"
-- remaining prefix.
--
-- Here is an example:
--
-- >> findEdge "ssip" (construct "mississippi")
-- >Just ((mkPrefix "ppi",Leaf),1)
--
-- This indicates that the edge @('mkPrefix' \"ppi\",'Leaf')@ matches,
-- and that we must strip 1 character from the string @\"ppi\"@ to get
-- the remaining prefix string @\"pi\"@.
--
-- Performance is linear in the length /n/ of the query list.
findEdge :: (Eq a) => [a] -> STree a -> Maybe (Edge a, Int)
findEdge _ (Leaf _) = Nothing
findEdge xs (Node es) = listToMaybe (mapMaybe pfx es)
    where pfx e@(p, t) = let p' = prefix p
                         in suffix p' xs >>= \suf ->
            case suf of
              [] -> return (e, length (zipWith const xs p'))
              s -> findEdge s t

-- | /O(n)/. Finds the subtree rooted at the end of the given query
-- sequence.  On failure, returns 'Nothing'.
--
-- Performance is linear in the length /n/ of the query list.
findTree :: (Eq a) => [a] -> STree a -> Maybe (STree a)
findTree s t = (snd . fst) `fmap` findEdge s t

-- | /O(n)/. Returns the path from the 'Edge' in the suffix tree at
-- which the given subsequence ends, up to the root of the tree.  If
-- the subsequence is not found, returns the empty list.
--
-- Performance is linear in the length of the query list.
findPath :: (Eq a) => [a] -> STree a -> [Edge a]
findPath = go []
    where go _ _ (Leaf _) = []
          go me xs (Node es) = pfx me es
              where pfx _ [] = []
                    pfx me (e@(p, t):es) =
                        case suffix (prefix p) xs of
                          Nothing -> pfx me es
                          Just [] -> e:me
                          Just s -> go (e:me) s t

-- | /O(t)/. Count the number of leaves in a tree.
--
-- Performance is linear in the number /t/ of elements in the tree.
countLeaves :: STree a -> Int
countLeaves (Leaf _) = 1
countLeaves (Node es) = L.foldl' (\v (_, t) -> countLeaves t + v) 0 es

-- | /O(n + r)/. Count the number of times a sequence is repeated
-- in the input sequence that was used to construct the suffix tree.
--
-- Performance is linear in the length /n/ of the input sequence, plus
-- the number of times /r/ the sequence is repeated.
countRepeats :: (Eq a) => [a] -> STree a -> Int
countRepeats s t = maybe 0 countLeaves (findTree s t)
