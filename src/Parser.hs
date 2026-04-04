{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeAbstractions #-}

-- | This module is a bit of a mess. There isn't really anything interesting in
-- it. For the most part it's been produced by an LLM because there isn't
-- anything in here that I wanted to illustrate.
module Parser
  ( -- * Raw AST
    RawExpr (..),
    Located (..),
    locOf,
    unLoc,

    -- * Parsers
    Parser,
    parseTy,
    parseExpr,
    parseModule,
  )
where

import Control.Monad.Combinators.Expr
import Data.Void (Void)
import Error.Diagnose
import Lambda qualified as Lambda
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as Lexer

---------------------------------------------------------------------------
--
-- Located wrapper
--
---------------------------------------------------------------------------

data Located a = Located Position a
  deriving (Show, Eq)

locOf :: Located a -> Position
locOf (Located p _) = p

unLoc :: Located a -> a
unLoc (Located _ a) = a

-- | Combine two positions into a span covering both.
spanPos :: Position -> Position -> Position
spanPos p1 p2 = Position (begin p1) (end p2) (file p1)

-- | Convert a megaparsec 'SourcePos' pair to a diagnose 'Position'.
toPosition :: SourcePos -> SourcePos -> Position
toPosition s e =
  Position
    (unPos (sourceLine s), unPos (sourceColumn s))
    (unPos (sourceLine e), unPos (sourceColumn e))
    (sourceName s)

-- | Wrap a parser's result with source position information.
located :: Parser a -> Parser (Located a)
located p = do
  s <- getSourcePos
  a <- p
  e <- getSourcePos
  pure $ Located (toPosition s e) a

---------------------------------------------------------------------------
--
-- Raw AST
--
---------------------------------------------------------------------------

data RawExpr
  = RVar String
  | RLit Int
  | RLam String (Maybe Lambda.Ty) (Located RawExpr)
  | RApp (Located RawExpr) (Located RawExpr)
  | RFix String (Maybe Lambda.Ty) (Located RawExpr)
  | RNil (Maybe Lambda.Ty)
  | RCons (Located RawExpr) (Located RawExpr)
  | RCaseList (Located RawExpr) (Located RawExpr) String String (Located RawExpr)
  | RLet String (Maybe Lambda.Ty) (Located RawExpr) (Located RawExpr)
  | RIfThenElse (Located RawExpr) (Located RawExpr) (Located RawExpr)
  | RNeg (Located RawExpr)
  | RAdd (Located RawExpr) (Located RawExpr)
  | RSub (Located RawExpr) (Located RawExpr)
  | RMul (Located RawExpr) (Located RawExpr)
  | RDiv (Located RawExpr) (Located RawExpr)
  | RBTrue
  | RBFalse
  | RIsZero (Located RawExpr)
  deriving (Show, Eq)

---------------------------------------------------------------------------
--
-- Lexer
--
---------------------------------------------------------------------------

type Parser = Parsec Void String

sc :: Parser ()
sc = Lexer.space space1 (Lexer.skipLineComment "--") (Lexer.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme sc

symbol :: String -> Parser String
symbol = Lexer.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

reserved :: [String]
reserved = ["Int", "Bool", "List", "fix", "nil", "case", "of", "if", "iszero", "then", "else", "let", "rec", "in", "true", "false"]

identifier :: Parser String
identifier = lexeme $ try $ do
  name <- (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_' <|> char '\'')
  if name `elem` reserved
    then fail $ "keyword " ++ show name ++ " is not a valid identifier"
    else pure name

integer :: Parser Int
integer = lexeme Lexer.decimal

---------------------------------------------------------------------------
--
-- Type parser
--
---------------------------------------------------------------------------

-- | Parse a type.
--
-- @
-- Int
-- List Int
-- Int -> Int
-- List Int -> Int -> List Int
-- @
parseTy :: Parser Lambda.Ty
parseTy = makeExprParser tyAtom [[InfixR (Lambda.TArr <$ symbol "->")]]

tyAtom :: Parser Lambda.Ty
tyAtom =
  choice
    [ Lambda.TInt <$ symbol "Int",
      Lambda.TBool <$ symbol "Bool",
      Lambda.TList <$> (symbol "List" *> tyAtom),
      parens parseTy
    ]

---------------------------------------------------------------------------
-- Expression parser
---------------------------------------------------------------------------

-- | Parse an expression.
--
-- @
-- 42
-- \\(x : Int). x + 1
-- fix (f : Int -> Int). \\(n : Int). if iszero n then 1 else n * f (n - 1)
-- nil \@Int
-- 1 :: 2 :: nil \@Int
-- case xs of { [] -> 0; h :: t -> h }
-- @
parseExpr :: Parser (Located RawExpr)
parseExpr = pExpr

-- | A binder: @(x : T)@ or just @x@ (unannotated).
binder :: Parser (String, Maybe Lambda.Ty)
binder =
  parens ((,) <$> identifier <*> optional (symbol ":" *> parseTy))
    <|> (,Nothing)
    <$> identifier

pExpr :: Parser (Located RawExpr)
pExpr =
  choice
    [ pLam,
      pFix,
      pLet,
      pIfThenElse,
      pCaseList,
      pCons
    ]

pLam :: Parser (Located RawExpr)
pLam = located $ do
  _ <- symbol "\\" <|> symbol "λ"
  (x, ty) <- binder
  _ <- symbol "."
  RLam x ty <$> pExpr

pFix :: Parser (Located RawExpr)
pFix = located $ do
  _ <- symbol "fix"
  (x, ty) <- binder
  _ <- symbol "."
  RFix x ty <$> pExpr

-- | @let (x : T) = e1 in e2@ or @let x = e1 in e2@
--   @let rec (x : T) = e1 in e2@ desugars to @let (x : T) = fix (x : T). e1 in e2@
--   @let (f : T) x1 ... xn = e1 in e2@ desugars to @let (f : T) = \x1. ... \xn. e1 in e2@
pLet :: Parser (Located RawExpr)
pLet = do
  s <- getSourcePos
  _ <- symbol "let"
  rec <- option False (True <$ symbol "rec")
  (x, ty) <- binder
  args <- many binder
  _ <- symbol "="
  e1 <- pExpr
  _ <- symbol "in"
  e2 <- pExpr
  e <- getSourcePos
  let pos = toPosition s e
  let e1' = foldr (\(a, aty) b -> Located pos (RLam a aty b)) e1 args
  let e1'' = if rec then Located pos (RFix x ty e1') else e1'
  pure $ Located pos (RLet x ty e1'' e2)

pIfThenElse :: Parser (Located RawExpr)
pIfThenElse = located $ do
  _ <- symbol "if"
  cond <- pCons
  _ <- symbol "then"
  e1 <- pExpr
  _ <- symbol "else"
  RIfThenElse cond e1 <$> pExpr

pCaseList :: Parser (Located RawExpr)
pCaseList = located $ do
  _ <- symbol "case"
  scrut <- pCons
  _ <- symbol "of"
  braces $ do
    _ <- symbol "[]"
    _ <- symbol "->"
    enil <- pExpr
    _ <- symbol ";"
    h <- identifier
    _ <- symbol "::"
    t <- identifier
    _ <- symbol "->"
    RCaseList scrut enil h t <$> pExpr

-- right-associative cons
pCons :: Parser (Located RawExpr)
pCons = do
  e <- pArith
  rest <- optional (symbol "::")
  case rest of
    Nothing -> pure e
    Just _ -> do
      r <- pCons
      pure $ Located (spanPos (locOf e) (locOf r)) (RCons e r)

pArith :: Parser (Located RawExpr)
pArith =
  makeExprParser
    pUnary
    [ [InfixL (binOp RMul <$ symbol "*"), InfixL (binOp RDiv <$ symbol "/")],
      [InfixL (binOp RAdd <$ symbol "+"), InfixL (binOp RSub <$ symbol "-")]
    ]
  where
    binOp f l r = Located (spanPos (locOf l) (locOf r)) (f l r)

pUnary :: Parser (Located RawExpr)
pUnary =
  choice
    [ located $ RNeg <$> (symbol "-" *> pUnary),
      located $ RIsZero <$> (symbol "iszero" *> pUnary),
      pApp
    ]

-- left-associative application
pApp :: Parser (Located RawExpr)
pApp = foldl1 (\l r -> Located (spanPos (locOf l) (locOf r)) (RApp l r)) <$> some pAtom

pAtom :: Parser (Located RawExpr)
pAtom =
  choice
    [ located $ RLit <$> integer,
      located $ RBTrue <$ symbol "true",
      located $ RBFalse <$ symbol "false",
      located pNilRaw,
      located $ RVar <$> identifier,
      located $ unLoc <$> parens pExpr
    ]

pNilRaw :: Parser RawExpr
pNilRaw = do
  _ <- symbol "nil"
  ty <- optional (symbol "@" *> tyAtom)
  pure $ RNil ty

-- | Parse a complete input (skip leading whitespace, expect EOF).
parseModule :: Parser (Located RawExpr)
parseModule = sc *> pExpr <* eof
