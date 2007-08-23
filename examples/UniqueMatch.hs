-- This module solves, more or less, the maximal unique match (MUM)
-- problem for two input lists, using a generalised suffix tree.
--
-- Unfortunately, we can't check for left maximality because we're
-- using lists instead of indices into arrays.  It's easy to look one
-- element to the left in an array, but you can't look one element
-- left of the head of a list.

module UniqueMatch (Sym(..), mkGenTree, maxUniqueMatches) where

import Data.SuffixTree (STree(..), construct, prefix)

-- We construct a generalised suffix tree, with elements annotated to
-- tell us whether they come from the left or right list.  Each list
-- is terminated with a stop symbol.
data Sym a = L a
           | Lx
           | R a
           | Rx
             deriving (Show)

isLeft (L _:_) = True
isLeft (Lx:_) = True
isLeft _ = False

isRight (R _:_) = True
isRight (Rx:_) = True
isRight _ = False

fromSyms (L a:ss) = a : fromSyms ss
fromSyms (R a:ss) = a : fromSyms ss
fromSyms (Lx:_) = []
fromSyms (Rx:_) = []
fromSyms _ = []

instance (Eq a) => Eq (Sym a) where
    L a == L b = a == b
    R a == R b = a == b
    L a == R b = a == b
    R a == L b = a == b
    Lx == Lx = True
    Rx == Rx = True
    _ == _ = False

instance (Ord a) => Ord (Sym a) where
    L a <= L b = a <= b
    R a <= R b = a <= b
    L a <= R b = a <= b
    R a <= L b = a <= b
    L _ <= Lx = True
    L _ <= Rx = True
    R _ <= Lx = True
    R _ <= Rx = True
    Lx <= Lx = True
    Rx <= Rx = True
    Lx <= Rx = True
    _ <= _ = False

mkGenTree :: (Ord a) => [a] -> [a] -> STree (Sym a)
mkGenTree a b = construct (map L a ++ Lx : map R b ++ [Rx])

maxUniqueMatches :: (Ord a) => STree (Sym a) -> [[a]]
maxUniqueMatches t = map (fromSyms . concatMap prefix . reverse)
                     (recurse [] t)
    where recurse _ Leaf = []
          recurse path (Node es) = loop path es

          loop path ((p, t):es) = matches ++ loop path es
              where matches | rightMaximal t = [p:path]
                            | otherwise = recurse (p:path) t
          loop _ _ = []

          rightMaximal (Node [(pa,Leaf), (pb,Leaf)]) =
                (isLeft a && isRight b) || (isRight a && isLeft b)
              where a = prefix pa
                    b = prefix pb
          rightMaximal _ = False
