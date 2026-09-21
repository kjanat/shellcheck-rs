{-# LANGUAGE MagicHash #-}
module Main (main) where

import Canary (forward, constant, add, subtractInt, multiply, composed, chained, shared,
  eqInt, neInt, ltInt, leInt, gtInt, geInt, minimumInt, selectInt, nestedBranch,
  operandBranches, scrutineeBranch, sharedBranch, branchCall)
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
    ["composed", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (composed x y))
    ["chained", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (chained x y))
    ["shared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (shared x y))
    ["eqInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (eqInt x y))
    ["neInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (neInt x y))
    ["ltInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (ltInt x y))
    ["leInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (leInt x y))
    ["gtInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (gtInt x y))
    ["geInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (geInt x y))
    ["minimumInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (minimumInt x y))
    ["selectInt", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (selectInt x y))
    ["nestedBranch", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (nestedBranch x y))
    ["operandBranches", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (operandBranches x y))
    ["scrutineeBranch", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (scrutineeBranch x y))
    ["sharedBranch", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (sharedBranch x y))
    ["branchCall", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (branchCall x y))
    _ -> fail "expected a canary entry and its integer arguments"
