{-# LANGUAGE MagicHash #-}
module Canary (forward, constant, add, subtractInt, multiply, composed, chained, shared,
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
  closureUnused, escapingRecursive, overApplied) where

import GHC.Exts (Int(I#), Int#, (+#), (-#), (*#), (==#), (/=#), (<#), (<=#), (>#), (>=#))
import Helpers (first)

{-# NOINLINE overApplied #-}
overApplied :: Int -> Int -> Int
overApplied x y = chooseFunction x y

{-# NOINLINE ignoreFunction #-}
ignoreFunction :: (Int -> Int) -> Int -> Int
ignoreFunction _ y = y

{-# NOINLINE closureUnused #-}
closureUnused :: Int -> Int -> Int
closureUnused x y = ignoreFunction (makeAdder x) y

{-# NOINLINE escapingRecursive #-}
escapingRecursive :: Int -> Int -> Int
escapingRecursive x y =
  let {-# NOINLINE go #-}
      go :: Int -> Int
      go (I# n) = case n <=# 0# of
        0# -> go (I# (n -# 1#))
        _ -> boxedSum x y
  in applyInt go (I# 7#)

{-# NOINLINE applyInt #-}
applyInt :: (Int -> Int) -> Int -> Int
applyInt f x = f x

{-# NOINLINE applyTwice #-}
applyTwice :: (Int -> Int) -> Int -> Int
applyTwice f x = f (f x)

{-# NOINLINE higherOrder #-}
higherOrder :: Int -> Int -> Int
higherOrder x y = applyTwice (\z -> boxedSum x z) y

{-# NOINLINE partialTop #-}
partialTop :: Int -> Int -> Int
partialTop x y = applyInt (boxedSum x) y

{-# NOINLINE localClosure #-}
localClosure :: Int -> Int -> Int
localClosure x y =
  let {-# NOINLINE addCaptured #-}
      addCaptured z = boxedSum x z
  in applyTwice addCaptured y

{-# NOINLINE makeAdder #-}
makeAdder :: Int -> (Int -> Int)
makeAdder x = case x of I# n -> \y -> boxedSum (I# n) y

{-# NOINLINE returnedClosure #-}
returnedClosure :: Int -> Int -> Int
returnedClosure x y = applyInt (makeAdder x) y

{-# NOINLINE chooseFunction #-}
chooseFunction :: Int -> (Int -> Int)
chooseFunction (I# n) = case n of
  0# -> \y -> y
  _ -> \y -> boxedSum (I# n) y

{-# NOINLINE closureBranch #-}
closureBranch :: Int -> Int -> Int
closureBranch x y = applyInt (chooseFunction x) y

data FunctionBox = FunctionBox (Int -> Int)

{-# NOINLINE useFunctionBox #-}
useFunctionBox :: FunctionBox -> Int -> Int
useFunctionBox (FunctionBox f) x = f x

{-# NOINLINE functionField #-}
functionField :: Int -> Int -> Int
functionField x y = useFunctionBox (FunctionBox (boxedSum x)) y

{-# NOINLINE recursiveTree #-}
recursiveTree :: Int# -> Int# -> Int#
recursiveTree n x = case n <=# 0# of
  0# -> recursiveTree (n -# 1#) x +# recursiveTree (n -# 1#) x
  _ -> x

{-# NOINLINE localLazy #-}
localLazy :: Int -> Int -> Int
localLazy x y =
  let {-# NOINLINE go #-}
      go :: Int -> Int -> Int
      go (I# n) unused = case n <=# 0# of
        0# -> go (I# (n -# 1#)) unused
        _ -> x
  in go (I# 7#) y

{-# NOINLINE recursiveSum #-}
recursiveSum :: Int# -> Int# -> Int#
recursiveSum n acc = case n <=# 0# of
  0# -> recursiveSum (n -# 1#) (acc +# n)
  _ -> acc

{-# NOINLINE mutualRecursion #-}
mutualRecursion :: Int# -> Int# -> Int#
mutualRecursion n acc = case n <=# 0# of
  0# -> mutualOther (n -# 1#) (acc +# 2#)
  _ -> acc

{-# NOINLINE mutualOther #-}
mutualOther :: Int# -> Int# -> Int#
mutualOther n acc = case n <=# 0# of
  0# -> mutualRecursion (n -# 1#) (acc -# 1#)
  _ -> acc

{-# NOINLINE localLoop #-}
localLoop :: Int# -> Int# -> Int#
localLoop n step =
  let go i acc = case i <=# 0# of
        0# -> go (i -# 1#) (acc +# step)
        _ -> acc
  in go n 0#

{-# NOINLINE localMutual #-}
localMutual :: Int# -> Int# -> Int#
localMutual n step =
  let evenGo i = case i <=# 0# of
        0# -> oddGo (i -# 1#)
        _ -> step
      oddGo i = case i <=# 0# of
        0# -> evenGo (i -# 1#)
        _ -> step +# 1#
  in evenGo n

{-# NOINLINE localJoin #-}
localJoin :: Int# -> Int# -> Int#
localJoin n x =
  let {-# NOINLINE finish #-}
      finish y = (y +# x) *# (y -# x)
  in case n of
    0# -> finish (x +# 1#)
    _ -> finish (x -# 2#)

{-# NOINLINE listSum #-}
listSum :: [Int] -> Int
listSum [] = I# 0#
listSum (x:xs) = boxedSum x (listSum xs)

{-# NOINLINE recursiveList #-}
recursiveList :: Int -> Int -> Int
recursiveList x y = listSum [x, y, x]

data Choice = Empty | One Int | Two Int Int
data Nested = Nested Choice Choice
data StrictPair = StrictPair !Int Int

{-# NOINLINE chooseData #-}
chooseData :: Int -> Int -> Choice
chooseData x@(I# n) y = case n of
  0# -> Empty
  1# -> One y
  _ -> Two x y

{-# NOINLINE readData #-}
readData :: Choice -> Int
readData c = case c of
  Empty -> I# 17#
  One x -> x
  Two x y -> boxedSum x y

{-# NOINLINE dataChoice #-}
dataChoice :: Int -> Int -> Int
dataChoice x y = readData (chooseData x y)

{-# NOINLINE firstPair #-}
firstPair :: Choice -> Int
firstPair (Two x _) = x
firstPair _ = I# 0#

{-# NOINLINE dataPair #-}
dataPair :: Int -> Int -> Int
dataPair x y = firstPair (Two x y)

{-# NOINLINE readNested #-}
readNested :: Nested -> Int
readNested (Nested a b) = case a of
  Empty -> readData b
  One x -> x
  Two x _ -> x

{-# NOINLINE dataNested #-}
dataNested :: Int -> Int -> Int
dataNested x y = readNested (Nested (chooseData x y) (One y))

{-# NOINLINE dataDefault #-}
dataDefault :: Int -> Int -> Int
dataDefault x y = firstPair (chooseData x y)

{-# NOINLINE dataLazy #-}
dataLazy :: Int -> Int -> Int
dataLazy x y = firstPair (Two x (boxedSum y y))

{-# NOINLINE readStrict #-}
readStrict :: StrictPair -> Int
readStrict (StrictPair _ y) = y

{-# NOINLINE dataStrict #-}
dataStrict :: Int -> Int -> Int
dataStrict x y = readStrict (StrictPair x y)

{-# NOINLINE readMaybe #-}
readMaybe :: Maybe Int -> Int
readMaybe Nothing = I# 0#
readMaybe (Just x) = x

{-# NOINLINE dataMaybe #-}
dataMaybe :: Int -> Int -> Int
dataMaybe x y = boxedSum (readMaybe (Just x)) (readMaybe Nothing)

{-# NOINLINE listFirst #-}
listFirst :: [Int] -> Int
listFirst [] = I# 0#
listFirst (x:_) = x

{-# NOINLINE dataList #-}
dataList :: Int -> Int -> Int
dataList x y = listFirst [x, y]

{-# NOINLINE inspectAgain #-}
inspectAgain :: Choice -> Int
inspectAgain c = case c of
  Empty -> I# 0#
  other -> readData other

{-# NOINLINE dataCaseBinder #-}
dataCaseBinder :: Int -> Int -> Int
dataCaseBinder x y = inspectAgain (chooseData x y)

{-# NOINLINE forward #-}
forward :: Int# -> Int# -> Int#
forward x y = first y x

{-# NOINLINE constant #-}
constant :: Int# -> Int#
constant x = first 42# x

{-# NOINLINE add #-}
add :: Int# -> Int# -> Int#
add x y = x +# y

{-# NOINLINE subtractInt #-}
subtractInt :: Int# -> Int# -> Int#
subtractInt x y = x -# y

{-# NOINLINE multiply #-}
multiply :: Int# -> Int# -> Int#
multiply x y = x *# y

{-# NOINLINE composed #-}
composed :: Int# -> Int# -> Int#
composed x y = (x +# y) *# (x -# y)

{-# NOINLINE chained #-}
chained :: Int# -> Int# -> Int#
chained x y = first (add x y) (subtractInt x y) *# y

{-# NOINLINE shared #-}
shared :: Int# -> Int# -> Int#
shared x y = case add x y of
  z -> first (z *# y) z -# z

{-# NOINLINE eqInt #-}
eqInt :: Int# -> Int# -> Int#
eqInt x y = x ==# y

{-# NOINLINE neInt #-}
neInt :: Int# -> Int# -> Int#
neInt x y = x /=# y

{-# NOINLINE ltInt #-}
ltInt :: Int# -> Int# -> Int#
ltInt x y = x <# y

{-# NOINLINE leInt #-}
leInt :: Int# -> Int# -> Int#
leInt x y = x <=# y

{-# NOINLINE gtInt #-}
gtInt :: Int# -> Int# -> Int#
gtInt x y = x ># y

{-# NOINLINE geInt #-}
geInt :: Int# -> Int# -> Int#
geInt x y = x >=# y

{-# NOINLINE minimumInt #-}
minimumInt :: Int# -> Int# -> Int#
minimumInt x y = case x <# y of
  0# -> y
  _ -> x

{-# NOINLINE selectInt #-}
selectInt :: Int# -> Int# -> Int#
selectInt x y = case x of
  -9223372036854775808# -> y -# 1#
  -1# -> y *# 2#
  0# -> add y 7#
  1# -> subtractInt y 3#
  9223372036854775807# -> y +# 1#
  other -> first other y

{-# NOINLINE nestedBranch #-}
nestedBranch :: Int# -> Int# -> Int#
nestedBranch x y = case add x y of
  z -> case z <# x of
    0# -> case y ==# 0# of
      0# -> multiply z y
      _ -> subtractInt z 1#
    _ -> case x of
      0# -> first y z
      _ -> add z x

{-# NOINLINE operandBranches #-}
operandBranches :: Int# -> Int# -> Int#
operandBranches x y =
  (case x of { 0# -> y; a -> a +# y }) *#
  (case y of { 1# -> x; b -> b -# x })

{-# NOINLINE scrutineeBranch #-}
scrutineeBranch :: Int# -> Int# -> Int#
scrutineeBranch x y = case (case x of { 0# -> y; a -> a -# y }) of
  0# -> add x y
  1# -> multiply x y
  z -> subtractInt z x

{-# NOINLINE sharedBranch #-}
sharedBranch :: Int# -> Int# -> Int#
sharedBranch x y = case add x y of
  z -> z +# (case z <# x of { 0# -> z *# y; _ -> z -# x })

{-# NOINLINE branchCall #-}
branchCall :: Int# -> Int# -> Int#
branchCall x y = first
  (case x of { 0# -> y; a -> a +# y })
  (case y of { 0# -> x; b -> b -# x })

{-# NOINLINE makeBox #-}
makeBox :: Int# -> Int# -> Int
makeBox x y = I# (x +# y)

{-# NOINLINE boxedSum #-}
boxedSum :: Int -> Int -> Int
boxedSum (I# x) (I# y) = I# (x +# y)

{-# NOINLINE boxedIgnore #-}
boxedIgnore :: Int -> Int -> Int
boxedIgnore x _ = x

{-# NOINLINE boxedChoose #-}
boxedChoose :: Int -> Int -> Int
boxedChoose x y = case x of
  I# n -> case n of { 0# -> y; _ -> x }

{-# NOINLINE boxedRoundTrip #-}
boxedRoundTrip :: Int# -> Int# -> Int#
boxedRoundTrip x y = case makeBox x y of I# z -> z

{-# NOINLINE boxedCaf #-}
boxedCaf :: Int
boxedCaf = I# 42#

{-# NOINLINE boxedShared #-}
boxedShared :: Int# -> Int# -> Int#
boxedShared x y = case boxedIgnore boxedCaf boxedCaf of I# z -> z +# x +# y

{-# NOINLINE boxedStrictIgnore #-}
boxedStrictIgnore :: Int -> Int -> Int
boxedStrictIgnore x y = case x of I# _ -> y

{-# NOINLINE lazyArgument #-}
lazyArgument :: Int -> Int -> Int
lazyArgument x y = boxedIgnore x (boxedSum y y)

{-# NOINLINE lazyLet #-}
lazyLet :: Int -> Int -> Int
lazyLet x y = let z = boxedSum x y in boxedSum z z

{-# NOINLINE lazyNested #-}
lazyNested :: Int -> Int -> Int
lazyNested x y =
  let a = boxedSum x y
      b = boxedSum a x
  in boxedSum b a

{-# NOINLINE lazyUnused #-}
lazyUnused :: Int -> Int -> Int
lazyUnused x y = let z = boxedSum y y in boxedIgnore x z

{-# NOINLINE lazyBranch #-}
lazyBranch :: Int -> Int -> Int
lazyBranch x y = boxedIgnore x (case y of I# n -> I# (n +# 1#))

{-# NOINLINE lazyStrictUse #-}
lazyStrictUse :: Int -> Int -> Int
lazyStrictUse x y = let z = boxedSum x y in case z of I# n -> I# (n +# n)
