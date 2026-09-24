module ShellCheckEntry (checkCodes, checkMessages, gccReport, parseMessages) where

import Control.Monad (guard)
import Data.Bits (shiftL, (.&.), (.|.))
import Data.Char (chr, isAscii, ord)
import Data.Functor.Identity (runIdentity)
import ShellCheck.Checker (checkScript)
import ShellCheck.Formatter.Format (colNo, codeNo, lineNo, makeNonVirtual, messageText, severityText)
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
