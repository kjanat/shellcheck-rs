module ShellCheckEntry (checkCodes, checkMessages, gccReport, lint, optional, parseMessages, version) where

import Control.Monad (guard)
import Data.Algorithm.Diff
import Data.Array (Array, ixmap, listArray, (!))
import Data.Bits (shiftL, (.&.), (.|.))
import Data.Char (chr, isAscii, ord)
import Data.Foldable (fold)
import Data.Function (on)
import Data.Functor.Identity (Identity, runIdentity)
import Data.List (groupBy, sortOn)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import qualified Data.Monoid as Monoid
import qualified ShellCheck.Analyzer
import ShellCheck.Checker (checkScript)
import ShellCheck.Data (shellForExecutable, shellcheckVersion)
import ShellCheck.Fixer (applyFix, mapPositions)
import ShellCheck.Formatter.Format (colNo, codeNo, lineNo, makeNonVirtual, messageText, severityText, sourceFile)
import ShellCheck.Interface
import ShellCheck.Parser (parseScript)

{-# NOINLINE checkCodes #-}
checkCodes :: String -> [Int]
checkCodes script =
  map (fromInteger . cCode . pcComment) . crComments . runIdentity $
    checkScript (mockedSystemInterface []) emptyCheckSpec {csScript = script}

{-# NOINLINE checkMessages #-}
checkMessages :: String -> [String]
checkMessages script =
  map (cMessage . pcComment) . crComments . runIdentity $
    checkScript (mockedSystemInterface []) emptyCheckSpec {csScript = script}

{-# NOINLINE parseMessages #-}
parseMessages :: String -> [String]
parseMessages script =
  map (cMessage . pcComment) . prComments . runIdentity $
    parseScript (mockedSystemInterface []) newParseSpec {psScript = script}

{-# NOINLINE gccReport #-}
gccReport :: FilePath -> String -> [String]
gccReport filename bytes =
  map (formatComment filename) . flip makeNonVirtual script . crComments . runIdentity $
    checkScript (mockedSystemInterface []) emptyCheckSpec {csFilename = filename, csScript = script}
  where
    script = decodeString bytes

{-# NOINLINE optional #-}
optional :: [(String, String, String, String)]
optional =
  [ (cdName c, cdDescription c, cdPositive c, cdNegative c)
  | c <- sortOn cdName ShellCheck.Analyzer.optionalChecks
  ]

{-# NOINLINE version #-}
version :: String
version = shellcheckVersion

type Span = (Int, Int, Int, Int)

type Edit = (Span, Bool, Int, String)

type Report = (Int, Int, String, Span, Span, Maybe [Edit], Maybe [Edit])

{-# NOINLINE lint #-}
lint
  :: Bool -> Bool -> [Int] -> Maybe [Int] -> Maybe String -> Int -> Maybe Bool -> [String]
  -> Maybe (FilePath, String)
  -> (FilePath -> Maybe Bool -> [FilePath] -> FilePath -> FilePath)
  -> (Maybe Bool -> FilePath -> Either String String)
  -> Bool -> Bool -> Maybe Bool
  -> FilePath -> String
  -> ([(FilePath, [(Int, String, Maybe [String], [Report])])], [Either (FilePath, String) String])
lint sourced ignoreRC excluded included shell severity extended optional rc find reader excerpts fixes diffColor filename bytes =
  (map report (groupBy ((==) `on` sourceFile) comments), maybe [] diffs diffColor)
  where
    comments = crComments . runIdentity $ checkScript system spec
    script = decodeString bytes
    system = (newSystemInterface :: SystemInterface Identity) {
        siReadFile = \external file -> return (fmap decodeString (reader external file)),
        siFindSource = \current external annotation original -> return (find current external annotation original),
        siGetConfig = \_ -> return (fmap (fmap decodeString) rc)
      }
    contents file = either (const "") decodeString (reader (Just True) file)
    report group =
      let name = sourceFile (head group)
          text = contents name
          fileLinesList = lines text
          lineCount = length fileLinesList
          fileLines = listArray (1, lineCount) fileLinesList
          line run =
            let lineNum = lineNo (fst (head run))
            in ( fromInteger lineNum
               , if lineNum < 1 || lineNum > toInteger lineCount then "" else fileLines ! fromInteger lineNum
               , if excerpts then fixedString (map fst run) fileLines else Nothing
               , map reported run
               )
      in (name, map line (groupBy ((==) `on` (lineNo . fst)) (zip group (makeNonVirtual group text))))
    reported (virtual, real) =
      ( level (severityText virtual)
      , fromInteger (codeNo virtual)
      , messageText virtual
      , extent (pcStartPos virtual) (pcEndPos virtual)
      , extent (pcStartPos real) (pcEndPos real)
      , edits virtual
      , edits real
      )
    edits c = if fixes then fmap (map edit . fixReplacements) (pcFix c) else Nothing
    edit r =
      ( extent (repStartPos r) (repEndPos r)
      , repInsertionPoint r == InsertAfter
      , repPrecedence r
      , repString r
      )
    extent start end = (fromInteger (posLine start), fromInteger (posColumn start), fromInteger (posLine end), fromInteger (posColumn end))
    diffs color =
      [ case reader (Just True) name of
          Right file -> Right (formatDoc (if color then colorize else nocolor) (makeDiff name (decodeString file) fix))
          Left msg -> Left (name, msg)
      | (name, fix) <- M.toList (buildFixMap (mapMaybe pcFix comments))
      ]
    spec = emptyCheckSpec {
        csFilename = filename,
        csScript = script,
        csCheckSourced = sourced,
        csIgnoreRC = ignoreRC,
        csExcludedWarnings = map toInteger excluded,
        csIncludedWarnings = fmap (map toInteger) included,
        csShellTypeOverride = shell >>= shellForExecutable,
        csMinSeverity = [ErrorC, WarningC, InfoC, StyleC] !! max 0 (min 3 severity),
        csExtendedAnalysis = extended,
        csOptionalChecks = optional
      }
    level text = case text of
      "error" -> 0
      "warning" -> 1
      "info" -> 2
      _ -> 3

sliceFile :: Fix -> Array Int String -> (Fix, Array Int String)
sliceFile fix lines =
    (mapPositions adjust fix, sliceLines lines)
  where
    (minLine, maxLine) =
        foldl (\(mm, mx) pos -> ((min mm $ fromIntegral $ posLine pos), (max mx $ fromIntegral $ posLine pos)))
                (maxBound, minBound) $
            concatMap (\x -> [repStartPos x, repEndPos x]) $ fixReplacements fix
    sliceLines :: Array Int String -> Array Int String
    sliceLines = ixmap (1, maxLine - minLine + 1) (\x -> x + minLine - 1)
    adjust pos =
        pos {
            posLine = posLine pos - (fromIntegral minLine) + 1
        }

fixedString :: [PositionedComment] -> Array Int String -> Maybe [String]
fixedString comments fileLines =
    case mapMaybe pcFix comments of
        [] -> Nothing
        fixes ->
            let mergedFix = fold fixes
                (excerptFix, excerpt) = sliceFile mergedFix fileLines
            in Just (applyFix excerptFix excerpt)

contextSize = 3
red = 31
green = 32
cyan = 36
bold = 1

nocolor n = id
colorize n s = (ansi n) ++ s ++ (ansi 0)
ansi n = "\x1B[" ++ show n ++ "m"

type ColorFunc = (Int -> String -> String)
data LFStatus = LinefeedMissing | LinefeedOk
data DiffDoc a = DiffDoc String LFStatus [DiffRegion a]
data DiffRegion a = DiffRegion (Int, Int) (Int, Int) [Diff a]

hasTrailingLinefeed str =
    case str of
        [] -> True
        _ -> last str == '\n'

coversLastLine regions =
    case regions of
        [] -> False
        _ -> (fst $ last regions)

makeDiff :: String -> String -> Fix -> DiffDoc String
makeDiff name contents fix = do
    let hunks = groupDiff $ computeDiff contents fix
    let lf = if coversLastLine hunks && not (hasTrailingLinefeed contents)
             then LinefeedMissing
             else LinefeedOk
    DiffDoc name lf $ findRegions hunks

computeDiff :: String -> Fix -> [Diff String]
computeDiff contents fix =
    let old = lines contents
        array = listArray (1, fromIntegral $ (length old)) old
        new = applyFix fix array
    in getDiff old new

groupDiff :: [Diff a] -> [(Bool, [Diff a])]
groupDiff = filter (\(_, l) -> not (null l)) . hunt []
  where
    hunt current [] = [(False, reverse current)]
    hunt current (x@Both {}:rest) = hunt (x:current) rest
    hunt current list =
        let (context, previous) = splitAt contextSize current
        in (False, reverse previous) : gather context 0 list

    gather current n [] =
        let (extras, patch) = splitAt (max 0 $ n - contextSize) current
        in [(True, reverse patch), (False, reverse extras)]

    gather current n list@(Both {}:_) | n == contextSize*2 =
        let (context, previous) = splitAt contextSize current
        in (True, reverse previous) : hunt context list

    gather current n (x@Both {}:rest) = gather (x:current) (n+1) rest
    gather current n (x:rest) = gather (x:current) 0 rest

findRegions :: [(Bool, [Diff String])] -> [DiffRegion String]
findRegions = find' 1 1
  where
    find' _ _ [] = []
    find' left right ((output, run):rest) =
        let (dl, dr) = countDelta run
            remainder = find' (left+dl) (right+dr) rest
        in
            if output
            then DiffRegion (left, dl) (right, dr) run : remainder
            else remainder

countDelta :: [Diff a] -> (Int, Int)
countDelta = count' 0 0
  where
    count' left right [] = (left, right)
    count' left right (x:rest) =
        case x of
            Both {} -> count' (left+1) (right+1) rest
            First {} -> count' (left+1) right rest
            Second {} -> count' left (right+1) rest

formatRegion :: ColorFunc -> LFStatus -> DiffRegion String -> String
formatRegion color lf (DiffRegion left right diffs) =
    let header = color cyan ("@@ -" ++ (tup left) ++ " +" ++ (tup right) ++" @@")
    in
        unlines $ header : reverse (getStrings lf (reverse diffs))
  where
    noLF = "\\ No newline at end of file"

    getStrings LinefeedOk list = map format list
    getStrings LinefeedMissing list@((Both _ _):_) = noLF : map format list
    getStrings LinefeedMissing list@((First _):_) = noLF : map format list
    getStrings LinefeedMissing (last:rest) = format last : getStrings LinefeedMissing rest

    tup (a,b) = (show a) ++ "," ++ (show b)
    format (Both x _) = ' ':x
    format (First x) = color red $ '-':x
    format (Second x) = color green $ '+':x

splitLast [] = ([], [])
splitLast x =
    let (last, rest) = splitAt 1 $ reverse x
    in (reverse rest, last)

formatDoc color (DiffDoc name lf regions) =
    let (most, last) = splitLast regions
    in
          (color bold $ "--- " ++ ("a" `combine` name)) ++ "\n" ++
          (color bold $ "+++ " ++ ("b" `combine` name)) ++ "\n" ++
          concatMap (formatRegion color LinefeedOk) most ++
          concatMap (formatRegion color lf) last

-- Matches filepath's POSIX (</>).
combine :: FilePath -> FilePath -> FilePath
combine a b
    | take 1 b == "/" = b
    | null a = b
    | null b = a
    | last a == '/' = a ++ b
    | otherwise = a ++ "/" ++ b

buildFixMap :: [Fix] -> M.Map String Fix
buildFixMap fixes = perFile
  where
    splitFixes = splitFixByFile $ mconcat fixes
    perFile = groupByMap (posFile . repStartPos . head . fixReplacements) splitFixes

splitFixByFile :: Fix -> [Fix]
splitFixByFile fix = map makeFix $ groupBy sameFile (fixReplacements fix)
  where
    sameFile rep1 rep2 = (posFile $ repStartPos rep1) == (posFile $ repStartPos rep2)
    makeFix reps = newFix { fixReplacements = reps }

groupByMap :: (Ord k, Monoid v) => (v -> k) -> [v] -> M.Map k v
groupByMap f = M.fromListWith Monoid.mappend . map (\x -> (f x, x))

formatComment :: FilePath -> PositionedComment -> String
formatComment filename c = concat [
    filename, ":",
    show $ lineNo c, ":",
    show $ colNo c, ": ",
    case severityText c of
        "error" -> "error"
        "warning" -> "warning"
        _ -> "note",
    ": ",
    concat . lines $ messageText c,
    " [SC", show $ codeNo c, "]"
  ]

decodeString :: String -> String
decodeString = decode
  where
    decode [] = []
    decode (c:rest) | isAscii c = c : decode rest
    decode (c:rest) =
        let num = (fromIntegral $ ord c) :: Int
            next = case num of
                _ | num >= 0xF8 -> Nothing
                  | num >= 0xF0 -> construct (num .&. 0x07) 3 rest
                  | num >= 0xE0 -> construct (num .&. 0x0F) 2 rest
                  | num >= 0xC0 -> construct (num .&. 0x1F) 1 rest
                  | True -> Nothing
        in
            case next of
                Just (n, remainder) -> chr n : decode remainder
                Nothing             -> c : decode rest

    construct x 0 rest = do
        guard $ x <= 0x10FFFF
        return (x, rest)
    construct x n (c:rest) =
        let num = (fromIntegral $ ord c) :: Int in
            if num >= 0x80 && num <= 0xBF
            then construct ((x `shiftL` 6) .|. (num .&. 0x3f)) (n-1) rest
            else Nothing
    construct _ _ _ = Nothing
