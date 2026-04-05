{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Main where

import Arith qualified
import Control.Monad
import Data.Map qualified as Map
import Error.Diagnose
import Lambda qualified as Lambda
import Options.Applicative
import Parser
import Prettyprinter (LayoutOptions (..), PageWidth (..), layoutPretty)
import Prettyprinter.Render.Text (renderIO)
import System.Exit (exitFailure)
import Text.Megaparsec (errorBundlePretty, parse)
import Typecheck

---------------------------------------------------------------------------
--
-- CLI
--
---------------------------------------------------------------------------

commandParser :: ParserInfo (IO ())
commandParser =
  info (commandP <**> helper) $
    fullDesc
      <> progDesc "Sheaf language demo"

commandP :: Options.Applicative.Parser (IO ())
commandP =
  subparser $
    command "run" (info (runP <**> helper) $ progDesc "Compile and run an expression of type Int -> Int")
      <> command "show" (info (showP <**> helper) $ progDesc "Compile an expression of type Int -> Int and print the lowered arithmetic expression")

runP :: Options.Applicative.Parser (IO ())
runP =
  runCommand
    <$> argument auto (metavar "N" <> help "Input integer")
    <*> argument str (metavar "EXPR" <> help "Expression of type Int -> Int")

showP :: Options.Applicative.Parser (IO ())
showP =
  showCommand
    <$> option auto (long "depth" <> short 'd' <> metavar "N" <> value 10 <> help "Maximum pretty-printing depth (default: 10)")
    <*> option auto (long "width" <> short 'w' <> metavar "COLS" <> value 80 <> help "Maximum line width (default: 80)")
    <*> argument str (metavar "EXPR" <> help "Expression of type Int -> Int")

---------------------------------------------------------------------------
--
-- Main
--
---------------------------------------------------------------------------

main :: IO ()
main = do
  join $ execParser commandParser

showCommand :: Int -> Int -> String -> IO ()
showCommand maxDepth width exprStr =
  case compileIntInt "<input>" exprStr of
    Left diag -> do
      printDiagnostic stderr WithUnicode (TabSize 4) defaultStyle diag
      exitFailure
    Right arithExpr -> do
      let opts = LayoutOptions (AvailablePerLine width 1.0)
      renderIO stdout (layoutPretty opts (Arith.prettyExprDepth maxDepth arithExpr))
      putStrLn ""

runCommand :: Int -> String -> IO ()
runCommand n exprStr =
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
