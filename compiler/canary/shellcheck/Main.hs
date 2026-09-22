module Main (main) where

import ShellCheck.AnalyzerLib (isDereferencingBinaryOp)
import qualified ShellCheck.Data as Data
import System.Environment (getArgs)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["isDereferencingBinaryOp", s] -> print (isDereferencingBinaryOp s)
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
