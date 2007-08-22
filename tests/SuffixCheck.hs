module Main where
import qualified Data.SuffixTree as T
import Data.Char (ord)
import Data.Maybe (isJust)
import Test.QuickCheck

instance Arbitrary Char where
  arbitrary     = choose ('a', 'z')
  coarbitrary c = variant (ord c `rem` 4)

deepCheck p = check (defaultConfig {configMaxTest = 1000}) p

prop_allsufs :: [Char] -> Bool
prop_allsufs s = let t = T.construct s
                 in all (`T.elem` t) (T.suffixes s)

prop_find_eq_elem :: [Char] -> Bool
prop_find_eq_elem s = all find_eq_elem (T.suffixes s)
    where t = T.construct s
          find_eq_elem s = isJust (T.find s t) == T.elem s t

main = do
  deepCheck prop_allsufs
  deepCheck prop_find_eq_elem
