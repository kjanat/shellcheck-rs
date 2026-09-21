{-# LANGUAGE MagicHash #-}
module Main (main) where

import Canary (forward, constant, add, subtractInt, multiply)
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
    ["add", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (add x y))
    ["subtractInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (subtractInt x y))
    ["multiply", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (multiply x y))
    _ -> fail "expected forward/add/subtractInt/multiply INT INT or constant INT"
