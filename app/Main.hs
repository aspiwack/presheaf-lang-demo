{-# LANGUAGE GADTs #-}

module Main where

import Arith qualified
import Error.Diagnose
import Parser (compileIntInt)
import System.Environment (getArgs)
import System.Exit (exitFailure)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [nStr, exprStr] -> do
      n <- case reads nStr of
        [(n', "")] -> pure (n' :: Int)
        _ -> do
          putStrLn "Error: first argument must be an integer"
          exitFailure
      case compileIntInt "<input>" exprStr of
        Left diag -> do
          printDiagnostic stderr WithUnicode (TabSize 4) defaultStyle diag
          exitFailure
        Right arithExpr ->
          case Arith.eval (Arith.VInt n) arithExpr of
            Left Arith.DivisionByZero -> do
              putStrLn "Error: division by zero"
              exitFailure
            Right (Arith.VInt result) ->
              print result
    _ -> do
      putStrLn "Usage: presheaf-lang-demo <number> '<expression>'"
      exitFailure
