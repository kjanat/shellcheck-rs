{-# LANGUAGE MagicHash #-}
module Main (main) where

import Canary (forward, constant)
import GHC.Exts (Int(I#))
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["forward", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (forward x y))
    ["constant", a] -> case read a of
      I# x -> print (I# (constant x))
    _ -> fail "expected forward INT INT or constant INT"
