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
  closureUnused, escapingRecursive, overApplied,
  polyTwoTypes, polyCrossModule, polyHigherOrder, polyRecursive, polyNested,
  classTwoInstances, classDefaultMethod, classSuperclass, classCrossModule,
  classParameterized, classMethodValue,
  charRoundTrip, charOrder, charSwitch, charField,
  stringLength, stringIndex, stringEmpty, stringUnicode, stringUnicodeIndex,
  stringNulByte, stringAppend, stringShared, stringUnused, stringLazyHead,
  stringHighLatin1, stringCount,
  newtypeRoundTrip, newtypeField, newtypeFunction, newtypeMonad, stringAppendShared,
  errorUnusedArgument, errorUnusedLet, errorUnusedShared, errorPlain,
  errorEmpty, errorUnicode, errorMultiline, errorUnboxed,
  errorComputed, errorBranch, errorLazyArgument, errorLazyShared, errorLazyField,
  errorNestedMessage, errorNul, errorNulNested, errorChar,
  tupleRoundTrip, tupleSwap, tupleSolo, tupleWide, tupleBoxed, tupleNested,
  tupleLazyComponent, tupleUnusedComponent,
  textWords, textLines, textFind, textReverse, textFilter, textMap,
  textSlice, textZip, textCompare, textUnicodeWords,
  stringEqual, stringEqualRule, stringEqualLazy, elemChar, elemString, elemLazy, prefixOf, prefixLazy,
  eqSpineOrder, eqRightSpine, eqElementOrder, elemSpineFirst, elemNeedleOrder, elemNeedleUnused, prefixOrder, prefixListOrder, prefixElementOrder,
  compareStrings, compareLazy, compareUnsigned,
  compareSpineOrder, compareRightSpine, compareElementOrder,
  tagColour, tagMaybe, colourEqual, colourCompare, pointerChoice,
  tagForced,
  mapChars, mapInts, mapFunctions, mapLazy, mapUnapplied,
  filterChars, filterLazy, takeWhileChars, takeWhileLazy, dropWhileChars, dropWhileLazy,
  reverseChars, reverseLazy, lengthChars, lengthLazy, consAppend, consAppendLazy,
  mapSpine, mapFunctionForced, filterPredicate, takeWhileElement, dropWhileSpine,
  reverseTail, lengthTail, consAppendRight)
import GHC.Exts (Int(I#))
import System.Environment (getArgs)

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["polyTwoTypes", a, b] -> print (polyTwoTypes (read a) (read b))
    ["polyCrossModule", a, b] -> print (polyCrossModule (read a) (read b))
    ["polyHigherOrder", a, b] -> print (polyHigherOrder (read a) (read b))
    ["polyRecursive", a, b] -> print (polyRecursive (read a) (read b))
    ["polyNested", a, b] -> print (polyNested (read a) (read b))
    ["classTwoInstances", a, b] -> print (classTwoInstances (read a) (read b))
    ["classDefaultMethod", a, b] -> print (classDefaultMethod (read a) (read b))
    ["classSuperclass", a, b] -> print (classSuperclass (read a) (read b))
    ["classCrossModule", a, b] -> print (classCrossModule (read a) (read b))
    ["classParameterized", a, b] -> print (classParameterized (read a) (read b))
    ["classMethodValue", a, b] -> print (classMethodValue (read a) (read b))
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
    ["charRoundTrip", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (charRoundTrip x y))
    ["charOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (charOrder x y))
    ["charSwitch", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (charSwitch x y))
    ["charField", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (charField x y))
    ["stringLength", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringLength x y))
    ["stringIndex", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringIndex x y))
    ["stringEmpty", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringEmpty x y))
    ["stringUnicode", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringUnicode x y))
    ["stringUnicodeIndex", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringUnicodeIndex x y))
    ["stringNulByte", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringNulByte x y))
    ["stringAppend", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringAppend x y))
    ["stringShared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringShared x y))
    ["stringUnused", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringUnused x y))
    ["stringLazyHead", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringLazyHead x y))
    ["stringHighLatin1", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringHighLatin1 x y))
    ["stringCount", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringCount x y))
    ["newtypeRoundTrip", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (newtypeRoundTrip x y))
    ["newtypeField", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (newtypeField x y))
    ["newtypeFunction", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (newtypeFunction x y))
    ["stringAppendShared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringAppendShared x y))
    ["errorUnusedArgument", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorUnusedArgument x y))
    ["errorUnusedLet", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorUnusedLet x y))
    ["errorUnusedShared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorUnusedShared x y))
    ["tupleRoundTrip", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleRoundTrip x y))
    ["tupleSwap", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleSwap x y))
    ["tupleSolo", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleSolo x y))
    ["tupleWide", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleWide x y))
    ["tupleBoxed", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleBoxed x y))
    ["tupleNested", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleNested x y))
    ["tupleLazyComponent", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleLazyComponent x y))
    ["tupleUnusedComponent", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tupleUnusedComponent x y))
    ["textWords", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textWords x y))
    ["textLines", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textLines x y))
    ["textFind", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textFind x y))
    ["textReverse", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textReverse x y))
    ["textFilter", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textFilter x y))
    ["textMap", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textMap x y))
    ["textSlice", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textSlice x y))
    ["textZip", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textZip x y))
    ["textCompare", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textCompare x y))
    ["textUnicodeWords", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (textUnicodeWords x y))
    ["stringEqual", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringEqual x y))
    ["stringEqualRule", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringEqualRule x y))
    ["stringEqualLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (stringEqualLazy x y))
    ["elemChar", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (elemChar x y))
    ["elemString", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (elemString x y))
    ["elemLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (elemLazy x y))
    ["prefixOf", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (prefixOf x y))
    ["prefixLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (prefixLazy x y))
    ["eqSpineOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (eqSpineOrder x y)
    ["eqRightSpine", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (eqRightSpine x y)
    ["eqElementOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (eqElementOrder x y)
    ["elemSpineFirst", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (elemSpineFirst x y)
    ["elemNeedleOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (elemNeedleOrder x y)
    ["elemNeedleUnused", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (elemNeedleUnused x y)
    ["prefixOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (prefixOrder x y)
    ["prefixListOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (prefixListOrder x y)
    ["prefixElementOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (prefixElementOrder x y)
    ["compareStrings", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (compareStrings x y))
    ["compareLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (compareLazy x y))
    ["compareUnsigned", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (compareUnsigned x y))
    ["compareSpineOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (compareSpineOrder x y)
    ["compareRightSpine", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (compareRightSpine x y)
    ["compareElementOrder", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (compareElementOrder x y)
    ["tagColour", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tagColour x y))
    ["tagMaybe", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (tagMaybe x y))
    ["colourEqual", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (colourEqual x y))
    ["colourCompare", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (colourCompare x y))
    ["pointerChoice", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (pointerChoice x y))
    ["tagForced", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (tagForced x y)
    ["errorPlain", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorPlain x y)
    ["errorNestedMessage", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorNestedMessage x y)
    ["errorNul", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorNul x y)
    ["errorChar", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorChar x y)
    ["errorNulNested", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorNulNested x y)
    ["errorComputed", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorComputed x y)
    ["errorBranch", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorBranch x y)
    ["errorLazyArgument", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorLazyArgument x y))
    ["errorLazyShared", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorLazyShared x y))
    ["errorLazyField", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorLazyField x y))
    ["errorUnboxed", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (errorUnboxed x y))
    ["errorEmpty", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorEmpty x y)
    ["errorUnicode", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorUnicode x y)
    ["errorMultiline", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (errorMultiline x y)
    ["mapChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (mapChars x y))
    ["mapLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (mapLazy x y))
    ["mapUnapplied", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (mapUnapplied x y))
    ["filterChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (filterChars x y))
    ["filterLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (filterLazy x y))
    ["takeWhileChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (takeWhileChars x y))
    ["takeWhileLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (takeWhileLazy x y))
    ["dropWhileChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (dropWhileChars x y))
    ["dropWhileLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (dropWhileLazy x y))
    ["reverseChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (reverseChars x y))
    ["reverseLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (reverseLazy x y))
    ["lengthChars", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (lengthChars x y))
    ["lengthLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (lengthLazy x y))
    ["consAppend", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (consAppend x y))
    ["consAppendLazy", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (consAppendLazy x y))
    ["mapInts", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (mapInts x y)
    ["mapFunctions", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (mapFunctions x y)
    ["mapSpine", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (mapSpine x y)
    ["mapFunctionForced", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (mapFunctionForced x y)
    ["filterPredicate", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (filterPredicate x y)
    ["takeWhileElement", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (takeWhileElement x y)
    ["dropWhileSpine", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (dropWhileSpine x y)
    ["reverseTail", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (reverseTail x y)
    ["lengthTail", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (lengthTail x y)
    ["consAppendRight", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (consAppendRight x y)
    ["newtypeMonad", a, b] -> case (read a, read b) of
      (I# x, I# y) -> print (I# (newtypeMonad x y))
    _ -> fail "expected a canary entry and its integer arguments"
