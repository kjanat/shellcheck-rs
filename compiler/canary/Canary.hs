{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
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
  closureUnused, escapingRecursive, overApplied,
  polyTwoTypes, polyCrossModule, polyHigherOrder, polyRecursive, polyNested,
  classTwoInstances, classDefaultMethod, classSuperclass, classCrossModule,
  classParameterized, classMethodValue,
  charRoundTrip, charOrder, charSwitch, charField,
  stringLength, stringIndex, stringEmpty, stringUnicode, stringUnicodeIndex,
  stringNulByte, stringAppend, stringShared, stringUnused, stringLazyHead,
  stringHighLatin1, stringCount, recursiveValue, recursiveValueUse,
  errorUnusedArgument, errorUnusedLet, errorUnusedShared, errorPlain,
  errorEmpty, errorUnicode, errorMultiline,
  tupleRoundTrip, tupleSwap, tupleSolo, tupleWide, tupleBoxed, tupleNested,
  tupleLazyComponent, tupleUnusedComponent,
  textWords, textLines, textFind, textReverse, textFilter, textMap,
  textSlice, textZip, textCompare, textUnicodeWords,
  newtypeRoundTrip, newtypeField, newtypeFunction, stringAppendShared) where

import GHC.Exts (Int(I#), Int#, (+#), (-#), (*#), (==#), (/=#), (<#), (<=#), (>#), (>=#),
  Char(C#), Char#, ord#, chr#, eqChar#, neChar#, ltChar#, leChar#, gtChar#, geChar#)
import Helpers (first, crossPoly, crossApply, Sized(..), Described(..), Small(..))

--------------------------------------------------------------------------------
-- Polymorphism: one function used at several types, across modules, as a
-- higher-order argument, and recursively.
--------------------------------------------------------------------------------

data Wrap = Wrap Int
data Pair a = Pair a a

{-# NOINLINE polyIdentity #-}
polyIdentity :: a -> a
polyIdentity x = x

{-# NOINLINE unwrap #-}
unwrap :: Wrap -> Int
unwrap (Wrap n) = n

-- The same binding at `Int` and at `Wrap`: two instances, one source.
{-# NOINLINE polyTwoTypes #-}
polyTwoTypes :: Int -> Int -> Int
polyTwoTypes x y = boxedSum (polyIdentity x) (unwrap (polyIdentity (Wrap y)))

-- `crossPoly` is defined in Helpers and instantiated here, at two types.
{-# NOINLINE polyCrossModule #-}
polyCrossModule :: Int -> Int -> Int
polyCrossModule x y = boxedSum (crossPoly (Wrap x) y) (crossPoly y x)

{-# NOINLINE bumpWrap #-}
bumpWrap :: Wrap -> Wrap
bumpWrap (Wrap n) = boxedSucc n `seq` Wrap (boxedSucc n)

{-# NOINLINE boxedSucc #-}
boxedSucc :: Int -> Int
boxedSucc (I# n) = I# (n +# 1#)

-- A polymorphic function taking a function argument, at two element types.
{-# NOINLINE polyHigherOrder #-}
polyHigherOrder :: Int -> Int -> Int
polyHigherOrder x y =
  boxedSum (crossApply boxedSucc x) (unwrap (crossApply bumpWrap (Wrap y)))

{-# NOINLINE polyCount #-}
polyCount :: [a] -> Int -> Int
polyCount [] acc = acc
polyCount (_:rest) acc = polyCount rest (boxedSucc acc)

-- Recursive specialization: the self-call reuses the instance it is inside.
{-# NOINLINE polyRecursive #-}
polyRecursive :: Int -> Int -> Int
polyRecursive x y =
  boxedSum (polyCount [x, y, x] (I# 0#)) (polyCount [Wrap x, Wrap y] y)

{-# NOINLINE firstOfPair #-}
firstOfPair :: Pair a -> a
firstOfPair (Pair a _) = a

-- A nested instance: the type argument is itself a constructor application.
{-# NOINLINE polyNested #-}
polyNested :: Int -> Int -> Int
polyNested x y =
  boxedSum (firstOfPair (Pair x y)) (firstOfPair (firstOfPair (Pair (Pair y x) (Pair x y))))

--------------------------------------------------------------------------------
-- Typeclasses: distinct instances, a default method, a superclass path, a
-- parameterized instance and a method used as a value.
--------------------------------------------------------------------------------

data Large = Large Int

instance Sized Large where
  size (Large n) = mulInt n (I# 3#)
  label _ = I# 5#

instance Described Large where
  describeIt v = mulInt (size v) (I# 7#)

instance Sized a => Sized (Pair a) where
  size p = boxedSum (size (firstOfPair p)) (label (firstOfPair p))

instance Described a => Described (Pair a)

{-# NOINLINE mulInt #-}
mulInt :: Int -> Int -> Int
mulInt (I# a) (I# b) = I# (a *# b)

-- Two instances of one class, each with its own method bodies.
{-# NOINLINE classTwoInstances #-}
classTwoInstances :: Int -> Int -> Int
classTwoInstances x y = boxedSum (size (Small x)) (size (Large y))

-- `Small` takes `Described`'s default `describeIt`; `Large` overrides it.
{-# NOINLINE classDefaultMethod #-}
classDefaultMethod :: Int -> Int -> Int
classDefaultMethod x y = boxedSum (describeIt (Small x)) (describeIt (Large y))

-- The default `weigh` reaches `size` through the superclass field of the
-- `Described` dictionary rather than through its own class.
{-# NOINLINE classSuperclass #-}
classSuperclass :: Int -> Int -> Int
classSuperclass x y = boxedSum (weigh (Small x)) (weigh (Large y))

-- `label` is a default method of a class declared in another module.
{-# NOINLINE classCrossModule #-}
classCrossModule :: Int -> Int -> Int
classCrossModule x y = boxedSum (label (Small x)) (label (Large y))

-- `Sized (Pair a)` is a dictionary built from another dictionary.
{-# NOINLINE classParameterized #-}
classParameterized :: Int -> Int -> Int
classParameterized x y =
  boxedSum (size (Pair (Small x) (Small y))) (describeIt (Pair (Large y) (Large x)))

{-# NOINLINE applySized #-}
applySized :: (Large -> Int) -> Int -> Int
applySized f n = f (Large n)

-- A class method passed as a value: the spine is absorbed into one instance
-- reference, and the call becomes an ordinary indirect application.
{-# NOINLINE classMethodValue #-}
classMethodValue :: Int -> Int -> Int
classMethodValue x y = boxedSum (applySized size x) (applySized describeIt y)

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

--------------------------------------------------------------------------------
-- Characters and string literals.
--
-- Every entry takes and returns Int#, so the existing integer CLI adapter can
-- drive it, but the work in between is Char# arithmetic and a [Char] built by
-- GHC.CString's unpackers. The traversals are written here rather than taken
-- from base, so what is compared against GHC is translated Haskell.
--------------------------------------------------------------------------------

-- chr# then ord# is the identity on a code point, including the boundaries.
{-# NOINLINE charRoundTrip #-}
charRoundTrip :: Int# -> Int# -> Int#
charRoundTrip x _ = ord# (chr# x)

-- All six Char# comparisons at once, packed into one Int#. Each returns 0 or 1,
-- so the result is a bit field and one wrong operator changes it.
{-# NOINLINE charOrder #-}
charOrder :: Int# -> Int# -> Int#
charOrder x y = case chr# x of
  a -> case chr# y of
    b -> (a `eqChar#` b)
      +# ((a `neChar#` b) *# 2#)
      +# ((a `ltChar#` b) *# 4#)
      +# ((a `leChar#` b) *# 8#)
      +# ((a `gtChar#` b) *# 16#)
      +# ((a `geChar#` b) *# 32#)

-- A switch whose scrutinee is a Char#, with literal alternatives.
{-# NOINLINE charSwitch #-}
charSwitch :: Int# -> Int# -> Int#
charSwitch x _ = case chr# x of
  'a'# -> 1#
  'z'# -> 26#
  '\n'# -> 100#
  _ -> 0#

-- A Char# inside a boxed Char, matched back out.
{-# NOINLINE charField #-}
charField :: Int# -> Int# -> Int#
charField x y = case C# (chr# x) of
  C# c -> case C# (chr# y) of
    C# d -> ord# c +# ord# d

{-# NOINLINE countChars #-}
countChars :: [Char] -> Int# -> Int#
countChars [] n = n
countChars (_ : cs) n = countChars cs (n +# 1#)

{-# NOINLINE sumChars #-}
sumChars :: [Char] -> Int# -> Int#
sumChars [] n = n
sumChars (C# c : cs) n = sumChars cs (n +# ord# c)

{-# NOINLINE indexChars #-}
indexChars :: [Char] -> Int# -> Int#
indexChars [] _ = -1#
indexChars (C# c : cs) n = case n ==# 0# of
  1# -> ord# c
  _ -> indexChars cs (n -# 1#)

-- Length of an ASCII literal: unpackCString# walked to its end.
{-# NOINLINE stringLength #-}
stringLength :: Int# -> Int# -> Int#
stringLength _ _ = countChars "shellcheck" 0#

-- Indexing past the end returns -1, so out-of-range is exercised too.
{-# NOINLINE stringIndex #-}
stringIndex :: Int# -> Int# -> Int#
stringIndex x _ = indexChars "shellcheck" x

-- The empty literal: no cell at all.
{-# NOINLINE stringEmpty #-}
stringEmpty :: Int# -> Int# -> Int#
stringEmpty _ _ = countChars "" 0#

-- Non-ASCII, so GHC emits unpackCStringUtf8# with modified UTF-8 bytes.
-- Two, three and four byte sequences, and a combining mark.
{-# NOINLINE stringUnicode #-}
stringUnicode :: Int# -> Int# -> Int#
stringUnicode _ _ = countChars "héllo wörld \955 \8364 \119070 e\769" 0#

{-# NOINLINE stringUnicodeIndex #-}
stringUnicodeIndex :: Int# -> Int# -> Int#
stringUnicodeIndex x _ = indexChars "héllo wörld \955 \8364 \119070 e\769" x

-- A NUL inside a literal, which GHC encodes as the overlong C0 80.
{-# NOINLINE stringNulByte #-}
stringNulByte :: Int# -> Int# -> Int#
stringNulByte x _ = indexChars "a\0\&b\0\&c" x

-- The top of Latin-1, which is still two UTF-8 bytes.
{-# NOINLINE stringHighLatin1 #-}
stringHighLatin1 :: Int# -> Int# -> Int#
stringHighLatin1 x _ = indexChars "\255\254\128\127" x

-- Two literals joined. At -O1 GHC folds this to one literal, so what it
-- covers is the folded form; `stringAppendShared` is the one that reaches
-- the appending unpacker.
{-# NOINLINE stringAppend #-}
stringAppend :: Int# -> Int# -> Int#
stringAppend x _ = indexChars ("shell" ++ "check") x

-- A literal appended to something GHC cannot fold into it. This is the shape
-- that becomes `unpackAppendCString#` at -O1 and `++` at -O0, and without it
-- the appending unpackers have no differential coverage at all.
{-# NOINLINE stringAppendShared #-}
stringAppendShared :: Int# -> Int# -> Int#
stringAppendShared x _ = indexChars ("say " ++ greeting) x

-- One literal read twice: the CAF must be shared, not rebuilt.
{-# NOINLINE stringShared #-}
stringShared :: Int# -> Int# -> Int#
stringShared x y = indexChars greeting x +# indexChars greeting y

{-# NOINLINE greeting #-}
greeting :: [Char]
greeting = "hello, world"

-- A traversal that is bound and never demanded. Walking the literal here
-- would be observable only as wasted work, so the check is that the lazy
-- argument still reaches `boxedIgnore` unforced.
{-# NOINLINE stringUnused #-}
stringUnused :: Int# -> Int# -> Int#
stringUnused x _ = case boxedIgnore (I# x) (I# (sumChars "never demanded" 0#)) of
  I# n -> n

-- Only the first character is demanded, so only it may be decoded.
{-# NOINLINE stringLazyHead #-}
stringLazyHead :: Int# -> Int# -> Int#
stringLazyHead _ _ = indexChars "abcdefghijklmnopqrstuvwxyz" 0#

-- The sum of every code point: the whole spine and every character.
{-# NOINLINE stringCount #-}
stringCount :: Int# -> Int# -> Int#
stringCount _ _ = sumChars "héllo wörld" 0#

-- A value defined in terms of itself. Its cells are a cycle, not a tree, and
-- this backend has no way to tie that knot: `Lazy::force` panics on re-entry
-- rather than looping. Emission must refuse it, which is what the canary
-- checks — a wrong answer here would be a miscompile, not a missing feature.
-- As an entry it is refused for its type; reached from one, for its cycle.
{-# NOINLINE recursiveValue #-}
recursiveValue :: [Char]
recursiveValue = 'x' : recursiveValue

{-# NOINLINE recursiveValueUse #-}
recursiveValueUse :: Int# -> Int# -> Int#
recursiveValueUse x _ = indexChars recursiveValue x

--------------------------------------------------------------------------------
-- Computations that would stop the program, never demanded.
--
-- `error` and its family are the bindings GHC's demand analysis marks as dead
-- ends: the call does not return. A thunk holding one is still an ordinary
-- value as long as nothing forces it, and these check exactly that — if the
-- backend evaluated a lazy binding eagerly, every one of them would abort
-- instead of answering, in every profile and at every input.
--
-- The errorUnused fixtures never force their errors. The four forced probes
-- below pin GHC's output while generated-code emission remains refused.
--------------------------------------------------------------------------------

-- Forced errorWithoutStackTrace messages, checked against the oracle only.
{-# NOINLINE errorPlain #-}
errorPlain :: Int# -> Int# -> Int
errorPlain _ _ = errorWithoutStackTrace "canary failure"

{-# NOINLINE errorEmpty #-}
errorEmpty :: Int# -> Int# -> Int
errorEmpty _ _ = errorWithoutStackTrace ""

{-# NOINLINE errorUnicode #-}
errorUnicode :: Int# -> Int# -> Int
errorUnicode _ _ = errorWithoutStackTrace "fout: λ 🐚"

{-# NOINLINE errorMultiline #-}
errorMultiline :: Int# -> Int# -> Int
errorMultiline _ _ = errorWithoutStackTrace "first\nsecond\n"

-- A failing argument passed to a function that ignores it.
{-# NOINLINE errorUnusedArgument #-}
errorUnusedArgument :: Int# -> Int# -> Int#
errorUnusedArgument x _ = case boxedIgnore (I# x) (error "never demanded") of
  I# n -> n

-- A failing computation bound by `let` and never demanded.
{-# NOINLINE errorUnusedLet #-}
errorUnusedLet :: Int# -> Int# -> Int#
errorUnusedLet x _ =
  let z = error "never demanded" :: Int
  in case boxedIgnore (I# x) z of I# n -> n

-- One failing thunk read twice, and ignored twice: sharing a dead end must
-- not force it either.
{-# NOINLINE errorUnusedShared #-}
errorUnusedShared :: Int# -> Int# -> Int#
errorUnusedShared x y =
  let z = error "never demanded" :: Int
  in case boxedIgnore (I# x) z of
       I# a -> case boxedIgnore (I# y) z of
         I# b -> a +# b

--------------------------------------------------------------------------------
-- Text-processing programs.
--
-- Whole algorithms rather than single operations: splitting, searching,
-- reversing, filtering, mapping, slicing, zipping and comparing. Each is
-- ordinary Haskell over `[Char]`, translated from its own Core — none of it is
-- a Rust implementation of the same idea wearing a Haskell name.
--
-- Together they walk literals end to end, build new lists cell by cell,
-- compare code points, and carry `Char#` through `ord#`/`chr#` arithmetic, so
-- a defect in the string machinery shows up as a wrong answer rather than as a
-- refusal.
--------------------------------------------------------------------------------

{-# NOINLINE countFields #-}
countFields :: Char# -> [Char] -> Int# -> Int#
countFields _ [] n = n +# 1#
countFields sep (C# c : cs) n = case eqChar# c sep of
  1# -> countFields sep cs (n +# 1#)
  _ -> countFields sep cs n

{-# NOINLINE textWords #-}
textWords :: Int# -> Int# -> Int#
textWords _ _ = countFields ' '# "the quick brown fox jumps over the lazy dog" 0#

{-# NOINLINE textLines #-}
textLines :: Int# -> Int# -> Int#
textLines _ _ = countFields '\n'# "one\ntwo\nthree\n" 0#

{-# NOINLINE textUnicodeWords #-}
textUnicodeWords :: Int# -> Int# -> Int#
textUnicodeWords _ _ = countFields ' '# "h\233llo w\246rld \955 \8364 \119070" 0#

{-# NOINLINE startsWith #-}
-- Matching two lists at once is not visibly exhaustive to GHC, which then
-- inserts a `patError` call. These are written so it does not have to: every
-- case below covers its scrutinee, so the algorithm is the subject rather than
-- GHC's incomplete-pattern machinery.
startsWith :: [Char] -> [Char] -> Int#
startsWith [] _ = 1#
startsWith (p : ps) haystack = case haystack of
  [] -> 0#
  (c : cs) -> case p of
    C# pc -> case c of
      C# cc -> case eqChar# pc cc of
        1# -> startsWith ps cs
        _ -> 0#

{-# NOINLINE indexOf #-}
indexOf :: [Char] -> [Char] -> Int# -> Int#
indexOf _ [] _ = -1#
indexOf needle haystack@(_ : cs) n = case startsWith needle haystack of
  1# -> n
  _ -> indexOf needle cs (n +# 1#)

{-# NOINLINE textFind #-}
textFind :: Int# -> Int# -> Int#
textFind _ _ = indexOf "brown" "the quick brown fox" 0#

{-# NOINLINE revOnto #-}
revOnto :: [Char] -> [Char] -> [Char]
revOnto [] acc = acc
revOnto (c : cs) acc = revOnto cs (c : acc)

{-# NOINLINE textReverse #-}
textReverse :: Int# -> Int# -> Int#
textReverse x _ = indexChars (revOnto "shellcheck" []) x

{-# NOINLINE keepBelow #-}
keepBelow :: Char# -> [Char] -> [Char]
keepBelow _ [] = []
keepBelow limit (C# c : cs) = case ltChar# c limit of
  1# -> C# c : keepBelow limit cs
  _ -> keepBelow limit cs

{-# NOINLINE textFilter #-}
textFilter :: Int# -> Int# -> Int#
textFilter _ _ = sumChars (keepBelow 'm'# "the quick brown fox") 0#

{-# NOINLINE shiftChars #-}
shiftChars :: Int# -> [Char] -> [Char]
shiftChars _ [] = []
shiftChars d (C# c : cs) = C# (chr# (ord# c +# d)) : shiftChars d cs

{-# NOINLINE textMap #-}
textMap :: Int# -> Int# -> Int#
textMap _ _ = sumChars (shiftChars 1# "abcxyz") 0#

{-# NOINLINE takeChars #-}
takeChars :: Int# -> [Char] -> [Char]
takeChars n cs = case n <=# 0# of
  1# -> []
  _ -> case cs of
    [] -> []
    (c : rest) -> c : takeChars (n -# 1#) rest

{-# NOINLINE dropChars #-}
dropChars :: Int# -> [Char] -> [Char]
dropChars n cs = case n <=# 0# of
  1# -> cs
  _ -> case cs of
    [] -> []
    (_ : rest) -> dropChars (n -# 1#) rest

-- The one that reads both inputs: every boundary pair slices differently.
{-# NOINLINE textSlice #-}
textSlice :: Int# -> Int# -> Int#
textSlice x y = sumChars (takeChars y (dropChars x "abcdefghijklmnopqrstuvwxyz")) 0#

{-# NOINLINE zipSum #-}
zipSum :: [Char] -> [Char] -> Int# -> Int#
zipSum [] _ n = n
zipSum (a : as) bs n = case bs of
  [] -> n
  (b : rest) -> case a of
    C# ac -> case b of
      C# bc -> zipSum as rest (n +# ord# ac *# ord# bc)

{-# NOINLINE textZip #-}
textZip :: Int# -> Int# -> Int#
textZip _ _ = zipSum "hello" "world!" 0#

{-# NOINLINE compareChars #-}
compareChars :: [Char] -> [Char] -> Int#
compareChars [] bs = case bs of
  [] -> 0#
  (_ : _) -> -1#
compareChars (a : as) bs = case bs of
  [] -> 1#
  (b : rest) -> case a of
    C# ac -> case b of
      C# bc -> case ltChar# ac bc of
        1# -> -1#
        _ -> case gtChar# ac bc of
          1# -> 1#
          _ -> compareChars as rest

{-# NOINLINE textCompare #-}
textCompare :: Int# -> Int# -> Int#
textCompare _ _ = compareChars "apple" "apricot"

--------------------------------------------------------------------------------
-- Unboxed tuples.
--
-- GHC's multi-value return. There is no box, no tag and no allocation: the
-- tuple *is* its components, side by side, and the type system guarantees one
-- is never bound lazily or stored in a lifted field. A `case` on one binds the
-- components and branches nowhere, because the family has one constructor.
--
-- A lifted component is still a lifted value, though, and `tupleLazyComponent`
-- is the one that says so: putting a thunk in an unboxed tuple must not force
-- it.
--------------------------------------------------------------------------------

{-# NOINLINE splitInt #-}
splitInt :: Int# -> Int# -> (# Int#, Int# #)
splitInt x y = (# x +# y, x -# y #)

{-# NOINLINE tupleRoundTrip #-}
tupleRoundTrip :: Int# -> Int# -> Int#
tupleRoundTrip x y = case splitInt x y of (# a, b #) -> a *# b

{-# NOINLINE tupleSwap #-}
tupleSwap :: Int# -> Int# -> Int#
tupleSwap x y = case splitInt x y of
  (# a, b #) -> case splitInt b a of
    (# c, d #) -> c -# d

{-# NOINLINE soloOf #-}
soloOf :: Int# -> (# Int# #)
soloOf x = (# x *# 3# #)

{-# NOINLINE tupleSolo #-}
tupleSolo :: Int# -> Int# -> Int#
tupleSolo x _ = case soloOf x of (# a #) -> a

{-# NOINLINE tripleOf #-}
tripleOf :: Int# -> Int# -> (# Int#, Int#, Int# #)
tripleOf x y = (# x, y, x *# y #)

{-# NOINLINE tupleWide #-}
tupleWide :: Int# -> Int# -> Int#
tupleWide x y = case tripleOf x y of (# a, b, c #) -> a +# b +# c

-- A lifted component: the tuple holds a boxed `Int` without forcing it.
{-# NOINLINE pairBoxed #-}
pairBoxed :: Int -> Int -> (# Int, Int #)
pairBoxed a b = (# a, b #)

{-# NOINLINE tupleBoxed #-}
tupleBoxed :: Int# -> Int# -> Int#
tupleBoxed x y = case pairBoxed (I# x) (I# y) of
  (# a, b #) -> case a of I# p -> case b of I# q -> p +# q

-- An unboxed tuple inside an unboxed tuple: the components nest, and so does
-- the Rust type built for them.
{-# NOINLINE nestOf #-}
nestOf :: Int# -> Int# -> (# (# Int#, Int# #), Int# #)
nestOf x y = (# (# x, y #), x +# y #)

{-# NOINLINE tupleNested #-}
tupleNested :: Int# -> Int# -> Int#
tupleNested x y = case nestOf x y of
  (# inner, s #) -> case inner of (# a, b #) -> a *# b +# s

-- A thunk in a component that is never demanded. Storing it must not force it.
{-# NOINLINE tupleLazyComponent #-}
tupleLazyComponent :: Int# -> Int# -> Int#
tupleLazyComponent x _ = case pairBoxed (I# x) (boxedSum (I# x) (I# x)) of
  (# a, _ #) -> case a of I# p -> p

-- A component the body never names at all.
{-# NOINLINE tupleUnusedComponent #-}
tupleUnusedComponent :: Int# -> Int# -> Int#
tupleUnusedComponent x y = case splitInt x y of (# a, _ #) -> a

--------------------------------------------------------------------------------
-- Newtypes.
--
-- A newtype has no runtime existence, so GHC turns every wrap and unwrap into
-- a cast rather than a constructor. Erasing one is sound exactly because both
-- sides are carried the same way, and these check that the value survives it.
--------------------------------------------------------------------------------

newtype Tag = Tag Int
newtype Wrapped a = Wrapped a
newtype Apply = Apply (Int -> Int)

{-# NOINLINE untag #-}
untag :: Tag -> Int
untag (Tag n) = n

-- Wrapped and unwrapped again: two casts and no allocation between them.
{-# NOINLINE newtypeRoundTrip #-}
newtypeRoundTrip :: Int# -> Int# -> Int#
newtypeRoundTrip x y = case untag (Tag (I# x)) of
  I# n -> case untag (Tag (I# y)) of
    I# m -> n +# m

-- A newtype wrapping a newtype, and a parameterised one at two arguments.
-- The unwrappers are top-level and monomorphic: a polymorphic local function
-- is a different question, and this one is about the carriers.
{-# NOINLINE unwrapTag #-}
unwrapTag :: Wrapped Tag -> Tag
unwrapTag (Wrapped a) = a

{-# NOINLINE unwrapInt #-}
unwrapInt :: Wrapped Int -> Int
unwrapInt (Wrapped a) = a

{-# NOINLINE newtypeField #-}
newtypeField :: Int# -> Int# -> Int#
newtypeField x y = case untag (unwrapTag (Wrapped (Tag (I# x)))) of
  I# n -> case unwrapInt (Wrapped (I# y)) of
    I# m -> n +# m

-- A newtype over a function: the carrier is the closure it wraps.
{-# NOINLINE newtypeFunction #-}
newtypeFunction :: Int# -> Int# -> Int#
newtypeFunction x y = case runApply (Apply (boxedSum (I# y))) (I# x) of
  I# n -> n

{-# NOINLINE runApply #-}
runApply :: Apply -> Int -> Int
runApply (Apply f) = f
