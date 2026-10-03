module Main (main) where

import Control.Exception (IOException, try)
import Control.Monad (foldM, unless)
import ShellCheck.AnalyzerLib (isDereferencingBinaryOp)
import ShellCheckEntry (checkCodes, checkMessages, gccReport, parseMessages)
import qualified ShellCheck.Data as Data
import System.Environment (getArgs)
import System.Exit (ExitCode (ExitFailure), exitWith)
import System.IO (IOMode (ReadMode), hGetContents, hPutStrLn, openBinaryFile, stderr)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["isDereferencingBinaryOp", s] -> print (isDereferencingBinaryOp s)
    ["parseMessages", s] -> print (parseMessages s)
    ["checkMessages", s] -> print (checkMessages s)
    ["checkCodes", s] -> print (checkCodes s)
    ("gccReport" : files) -> lint files
    ["shellForExecutable", s] -> print (Data.shellForExecutable s)
    ["internalVariables"] -> print Data.internalVariables
    ["specialIntegerVariables"] -> print Data.specialIntegerVariables
    ["specialVariablesWithoutSpaces"] -> print Data.specialVariablesWithoutSpaces
    ["arrayVariables"] -> print Data.arrayVariables
    ["commonCommands"] -> print Data.commonCommands
    ["nonReadingCommands"] -> print Data.nonReadingCommands
    ["sampleWords"] -> print Data.sampleWords
    ["binaryTestOps"] -> print Data.binaryTestOps
    ["arithmeticBinaryTestOps"] -> print Data.arithmeticBinaryTestOps
    ["unaryTestOps"] -> print Data.unaryTestOps
    ["flagsForRead"] -> print Data.flagsForRead
    ["flagsForMapfile"] -> print Data.flagsForMapfile
    ["declaringCommands"] -> print Data.declaringCommands
    ["privilegeElevationCommands"] -> print Data.privilegeElevationCommands
    _ -> errorWithoutStackTrace ("unknown entry: " ++ show arguments)

lint :: [FilePath] -> IO ()
lint [] = hPutStrLn stderr "No files specified." >> exitWith (ExitFailure 3)
lint files = do
  status <- foldM check 0 files
  unless (status == 0) $ exitWith (ExitFailure status)
  where
    check status file = do
      input <- try (readBinary file) :: IO (Either IOException String)
      case input of
        Left e -> hPutStrLn stderr (file ++ ": " ++ show e) >> return (max status 2)
        Right bytes -> do
          let report = gccReport file bytes
          mapM_ putStrLn report
          return (if null report then status else max status 1)
    readBinary file = do
      handle <- openBinaryFile file ReadMode
      bytes <- hGetContents handle
      length bytes `seq` return bytes
