module Main where
import qualified Data.SuffixTree as T
import Data.Char (ord)
import Data.List (inits)
import Data.Maybe (isJust)
import Test.QuickCheck

instance Arbitrary Char where
  arbitrary     = choose ('a', 'z')
  coarbitrary c = variant (ord c `rem` 4)

deepCheck p = check (defaultConfig {configMaxTest = 1000}) p

prop_allsuffixes :: [Char] -> Bool
prop_allsuffixes s = let t = T.construct s
                     in all (`T.elem` t) (T.suffixes s)

prefixes = tail . inits

prop_allinfixes :: [Char] -> Bool
prop_allinfixes s = let t = T.construct s
                    in all (\suf -> all (`T.elem` t) (prefixes suf)) (T.suffixes s)

prop_findEdge_eqv_elem :: [Char] -> Bool
prop_findEdge_eqv_elem s = all check (T.suffixes s)
    where t = T.construct s
          check s = isJust (T.findEdge s t) == T.elem s t

prop_findEdge_eqv_findTree :: [Char] -> Bool
prop_findEdge_eqv_findTree s = all check (T.suffixes s)
    where t = T.construct s
          check s = isJust (T.findEdge s t) == isJust (T.findTree s t)

prop_findEdge_eqv_findPath :: [Char] -> Bool
prop_findEdge_eqv_findPath s = all check (T.suffixes s)
    where t = T.construct s
          check s = isJust (T.findEdge s t) == (not . null) (T.findPath s t)

main = do
  deepCheck prop_allsuffixes
  quickCheck prop_allinfixes
  deepCheck prop_findEdge_eqv_elem
  deepCheck prop_findEdge_eqv_findTree
  deepCheck prop_findEdge_eqv_findPath
