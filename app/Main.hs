{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Main where

import Arith qualified
import Data.Map qualified as Map
import Error.Diagnose
import Lambda qualified as Lambda
import Parser
import System.Environment (getArgs)
import System.Exit (exitFailure)
import Text.Megaparsec
import Typecheck

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

---------------------------------------------------------------------------
--
-- Compilation pipeline
--
---------------------------------------------------------------------------

-- | Parse a string as a Lambda expression, typecheck it against @Int -> Int@,
-- and lower it to an arithmetic expression via the presheaf interpretation.
compileIntInt :: FilePath -> String -> Either (Diagnostic String) (Arith.Expr 'Arith.TInt 'Arith.TInt)
compileIntInt filename input = do
  raw <- case parse parseModule filename input of
    Left parseErr ->
      Left $
        addReport (addFile mempty filename input) $
          Err Nothing (errorBundlePretty parseErr) [] []
    Right r -> Right r
  case check raw (Lambda.SArr Lambda.SInt Lambda.SInt) Map.empty of
    Left tcErr -> Left $ tcErrorToDiagnostic filename input tcErr
    Right kexpr -> Right $ Lambda.lower (kexpr id Empty)
