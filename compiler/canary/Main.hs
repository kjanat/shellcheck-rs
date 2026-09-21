{-# LANGUAGE MagicHash #-}
module Main (main) where

import Canary (forward, constant, add, subtractInt, multiply, composed, chained, shared,
  eqInt, neInt, ltInt, leInt, gtInt, geInt, minimumInt, selectInt, nestedBranch,
  operandBranches, scrutineeBranch, sharedBranch, branchCall,
  makeBox, boxedSum, boxedIgnore, boxedChoose, boxedRoundTrip, boxedShared,
  boxedStrictIgnore, boxedCaf,
  lazyArgument, lazyLet, lazyNested, lazyUnused, lazyBranch, lazyStrictUse,
  dataChoice, dataPair, dataNested, dataDefault, dataLazy, dataStrict,
  dataMaybe, dataList, dataCaseBinder,
  recursiveSum, mutualRecursion, localLoop, localMutual, localJoin, recursiveList,
  recursiveTree, localLazy,
  higherOrder, partialTop, localClosure, returnedClosure, closureBranch, functionField,
  closureUnused, escapingRecursive, overApplied)
import GHC.Exts (Int(I#))
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["overApplied", a, b] -> print (overApplied (read a) (read b))
    ["closureUnused", a, b] -> print (closureUnused (read a) (read b))
    ["escapingRecursive", a, b] -> print (escapingRecursive (read a) (read b))
    ["higherOrder", a, b] -> print (higherOrder (read a) (read b))
    ["partialTop", a, b] -> print (partialTop (read a) (read b))
    ["localClosure", a, b] -> print (localClosure (read a) (read b))
    ["returnedClosure", a, b] -> print (returnedClosure (read a) (read b))
    ["closureBranch", a, b] -> print (closureBranch (read a) (read b))
    ["functionField", a, b] -> print (functionField (read a) (read b))
    ["recursiveTree", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (recursiveTree x y))
    ["localLazy", a, b] -> print (localLazy (read a) (read b))
    ["recursiveSum", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (recursiveSum x y))
    ["mutualRecursion", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (mutualRecursion x y))
    ["localLoop", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (localLoop x y))
    ["localMutual", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (localMutual x y))
    ["localJoin", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (localJoin x y))
    ["recursiveList", a, b] -> print (recursiveList (read a) (read b))
    ["dataChoice", a, b] -> print (dataChoice (read a) (read b))
    ["dataPair", a, b] -> print (dataPair (read a) (read b))
    ["dataNested", a, b] -> print (dataNested (read a) (read b))
    ["dataDefault", a, b] -> print (dataDefault (read a) (read b))
    ["dataLazy", a, b] -> print (dataLazy (read a) (read b))
    ["dataStrict", a, b] -> print (dataStrict (read a) (read b))
    ["dataMaybe", a, b] -> print (dataMaybe (read a) (read b))
    ["dataList", a, b] -> print (dataList (read a) (read b))
    ["dataCaseBinder", a, b] -> print (dataCaseBinder (read a) (read b))
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
    ["makeBox", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (makeBox x y)
    ["boxedSum", a, b] -> print (boxedSum (read a) (read b))
    ["boxedIgnore", a, b] -> print (boxedIgnore (read a) (read b))
    ["boxedChoose", a, b] -> print (boxedChoose (read a) (read b))
    ["boxedStrictIgnore", a, b] -> print (boxedStrictIgnore (read a) (read b))
    ["boxedRoundTrip", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (boxedRoundTrip x y))
    ["boxedShared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (boxedShared x y))
    ["boxedCaf"] -> print boxedCaf
    ["lazyArgument", a, b] -> print (lazyArgument (read a) (read b))
    ["lazyLet", a, b] -> print (lazyLet (read a) (read b))
    ["lazyNested", a, b] -> print (lazyNested (read a) (read b))
    ["lazyUnused", a, b] -> print (lazyUnused (read a) (read b))
    ["lazyBranch", a, b] -> print (lazyBranch (read a) (read b))
    ["lazyStrictUse", a, b] -> print (lazyStrictUse (read a) (read b))
    _ -> fail "expected a canary entry and its integer arguments"
