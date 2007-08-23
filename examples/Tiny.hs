module Main where

import qualified Data.SuffixTree as S
import System.Environment (getArgs)

main = do
  [fileName, cons] <- getArgs
  let ctor = case cons of
               "1" -> S.constructWith [minBound..maxBound]
               "2" -> S.construct
  tree <- ctor `fmap` readFile fileName
  putStrLn (show (S.fold id id (\_ a _ -> a+1) id 0 tree) ++ " edges")
  (lines `fmap` getContents) >>= mapM_ (print . (`S.elem` tree))
