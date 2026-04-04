{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeAbstractions #-}

module Parser
  ( -- * Raw AST
    RawExpr (..),

    -- * Parsers
    Parser,
    parseTy,
    parseExpr,
    parseModule,

    -- * Typechecker
    infer,
    check,

    -- * Compilation
    compileIntInt,
  )
where

import Arith qualified
import Control.Monad.Combinators.Expr
import Data.Kind
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Type.Equality
import Data.Void (Void)
import GHC.Exts (WithDict (..))
import Lambda qualified as Lambda
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

---------------------------------------------------------------------------
-- Raw AST
---------------------------------------------------------------------------

data RawExpr
  = RVar String
  | RLit Int
  | RLam String (Maybe Lambda.Ty) RawExpr
  | RApp RawExpr RawExpr
  | RFix String (Maybe Lambda.Ty) RawExpr
  | RNil (Maybe Lambda.Ty)
  | RCons RawExpr RawExpr
  | RCaseList RawExpr RawExpr String String RawExpr
  | RLet String (Maybe Lambda.Ty) RawExpr RawExpr
  | RIfThenElse RawExpr RawExpr RawExpr
  | RNeg RawExpr
  | RAdd RawExpr RawExpr
  | RSub RawExpr RawExpr
  | RMul RawExpr RawExpr
  | RDiv RawExpr RawExpr
  | RBTrue
  | RBFalse
  | RIsZero RawExpr
  deriving (Show, Eq)

type Env :: (Lambda.Ty -> Type) -> [Lambda.Ty] -> Type
data Env w γ where
  Empty :: Env w '[]
  Extend :: (Lambda.KnownTy ty) => w ty -> (forall ρ. (Lambda.KnownTy ρ) => w' ρ -> w ρ) -> Env w' y -> Env w (ty ': y)

mapEnv :: (forall ty. (Lambda.KnownTy ty) => w ty -> w' ty) -> Env w γ -> Env w' γ
mapEnv _ Empty = Empty
mapEnv f (Extend w k env) = Extend (f w) (f . k) env

type Var :: [Lambda.Ty] -> Lambda.Ty -> Type
data Var γ ty where
  Here :: Var (ty ': γ) ty
  There :: Var γ ty -> Var (ty' ': γ) ty

lookupVar :: Var γ ty -> Env w γ -> w ty
lookupVar = go id
  where
    go :: (forall ρ. (Lambda.KnownTy ρ) => w' ρ -> w ρ) -> Var γ ty -> Env w' γ -> w ty
    go k Here (Extend w _ _) = k w
    go k (There v) (Extend _ k' env) = go (k . k') v env

-- Basically encodes (typed) de Bruijn indices without creating a new type.
type KExpr v γ ty = forall w. (forall ρ. (Lambda.KnownTy ρ) => v ρ -> w ρ) -> Env w γ -> Lambda.Expr w ty

kvar :: Var γ ty -> KExpr v γ ty
kvar w _k env = Lambda.Var (lookupVar w env)

klit :: Int -> KExpr v γ Lambda.TInt
klit n _k _env = Lambda.Lit n

klam :: Lambda.STy ty -> KExpr v (ty ': γ) s -> KExpr v γ (Lambda.TArr ty s)
klam @ty s e k env = Lambda.Lam s $ \k' v ->
  withDict @(Lambda.KnownTy ty) s $
    e (k' . k) (Extend v k' env)

kapp :: KExpr v γ (Lambda.TArr s t) -> KExpr v γ s -> KExpr v γ t
kapp e1 e2 k env = Lambda.App (e1 k env) (e2 k env)

kfix :: forall ty v γ. Lambda.STy ty -> KExpr v (ty ': γ) ty -> KExpr v γ ty
kfix s e k env = Lambda.Fix s $ \k' v ->
  withDict @(Lambda.KnownTy ty) s $
    e (k' . k) (Extend v k' env)

knil :: Lambda.STy ty -> KExpr v γ (Lambda.TList ty)
knil s _k _env = Lambda.Nil s

kcons :: KExpr v γ ty -> KExpr v γ (Lambda.TList ty) -> KExpr v γ (Lambda.TList ty)
kcons e1 e2 k env = Lambda.Cons (e1 k env) (e2 k env)

kcaselist :: forall σ v γ ty. Lambda.STy σ -> Lambda.STy ty -> KExpr v γ (Lambda.TList σ) -> KExpr v γ ty -> KExpr v (σ ': Lambda.TList σ ': γ) ty -> KExpr v γ ty
kcaselist sEv tyEv scrut enil econs k env =
  withDict @(Lambda.KnownTy σ) sEv $
    withDict @(Lambda.KnownTy ty) tyEv $
      Lambda.CaseList (scrut k env) (enil k env) $ \k' h t ->
        econs (k' . k) (Extend h id (Extend t k' env))

kifthenelse :: Lambda.STy ty -> KExpr v γ 'Lambda.TBool -> KExpr v γ ty -> KExpr v γ ty -> KExpr v γ ty
kifthenelse @ty tyEv e e1 e2 k env =
  withDict @(Lambda.KnownTy ty) tyEv $
    Lambda.IfThenElse (e k env) (e1 k env) (e2 k env)

kneg :: KExpr v γ 'Lambda.TInt -> KExpr v γ 'Lambda.TInt
kneg e k env = Lambda.Neg (e k env)

kbtrue :: KExpr v γ 'Lambda.TBool
kbtrue _k _env = Lambda.BTrue

kbfalse :: KExpr v γ 'Lambda.TBool
kbfalse _k _env = Lambda.BFalse

kiszero :: KExpr v γ 'Lambda.TInt -> KExpr v γ 'Lambda.TBool
kiszero e k env = Lambda.IsZero (e k env)

karith ::
  (forall w. Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt) ->
  KExpr v γ 'Lambda.TInt ->
  KExpr v γ 'Lambda.TInt ->
  KExpr v γ 'Lambda.TInt
karith op e1 e2 k env = op (e1 k env) (e2 k env)

data UKExpr v γ where
  MkUexpr :: Lambda.STy ty -> KExpr v γ ty -> UKExpr v γ

extendEnv :: UKExpr v γ -> UKExpr v (ty ': γ)
extendEnv (MkUexpr s e) = MkUexpr s $ \k env -> case env of
  Extend _ k' env' -> e k (mapEnv k' env')

klit' :: Int -> Maybe (UKExpr v γ)
klit' n = Just $ MkUexpr Lambda.SInt (klit n)

---------------------------------------------------------------------------
-- Bidirectional typechecker
---------------------------------------------------------------------------

-- | Infer the type of an expression (synthesis mode).
infer :: RawExpr -> Map String (UKExpr v γ) -> Maybe (UKExpr v γ)
infer (RVar x) env = Map.lookup x env
infer (RLit n) _ = klit' n
infer (RLam _ Nothing _) _ = Nothing -- can't infer unannotated lambda
infer (RLam x (Just ty) e) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    MkUexpr sRes e' <- infer e env'
    Just $ MkUexpr (Lambda.SArr sTy sRes) (klam sTy e')
infer (RLet x Nothing e1 e2) env = do
  MkUexpr s1 e1' <- infer e1 env
  let env' = Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env)
  MkUexpr s2 e2' <- infer e2 env'
  Just $ MkUexpr s2 (kapp (klam s1 e2') e1')
infer (RLet x (Just ty) e1 e2) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    e1' <- check e1 sTy env
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    MkUexpr s2 e2' <- infer e2 env'
    Just $ MkUexpr s2 (kapp (klam sTy e2') e1')
infer (RApp e1 e2) env = do
  e1' <- infer e1 env
  case e1' of
    MkUexpr (Lambda.SArr s1 s2) e1'' -> do
      e2' <- check e2 s1 env
      Just $ MkUexpr s2 (kapp e1'' e2')
    _ -> Nothing
infer (RFix _ Nothing _) _ = Nothing -- can't infer unannotated fix
infer (RFix x (Just ty) e) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    e' <- check e sTy env'
    Just $ MkUexpr sTy (kfix sTy e')
infer (RNil Nothing) _ = Nothing -- can't infer unannotated nil
infer (RNil (Just ty)) _ = case Lambda.sty ty of
  Lambda.SomeSTy s -> Just $ MkUexpr (Lambda.SList s) (knil s)
infer (RCons e1 e2) env = do
  MkUexpr s2 e2' <- infer e2 env
  case s2 of
    Lambda.SList sElem -> do
      e1' <- check e1 sElem env
      Just $ MkUexpr s2 (kcons e1' e2')
    _ -> Nothing
infer (RCaseList scrut enil hd tl econs) env = do
  MkUexpr sScrut scrut' <- infer scrut env
  case sScrut of
    Lambda.SList sElem -> do
      MkUexpr sRes enil' <- infer enil env
      let env' =
            Map.insert hd (MkUexpr sElem (kvar Here)) $
              Map.insert tl (MkUexpr (Lambda.SList sElem) (kvar (There Here))) $
                Map.map (extendEnv . extendEnv) env
      econs' <- check econs sRes env'
      Just $ MkUexpr sRes (kcaselist sElem sRes scrut' enil' econs')
    _ -> Nothing
infer (RIfThenElse e e1 e2) env = do
  e' <- check e Lambda.SBool env
  MkUexpr s e1' <- infer e1 env
  e2' <- check e2 s env
  Just $ MkUexpr s (kifthenelse s e' e1' e2')
infer RBTrue _ = Just $ MkUexpr Lambda.SBool kbtrue
infer RBFalse _ = Just $ MkUexpr Lambda.SBool kbfalse
infer (RIsZero e) env = do
  e' <- check e Lambda.SInt env
  Just $ MkUexpr Lambda.SBool (kiszero e')
infer (RNeg e) env = do
  e' <- check e Lambda.SInt env
  Just $ MkUexpr Lambda.SInt (kneg e')
infer (RAdd e1 e2) env = inferArith Lambda.Add e1 e2 env
infer (RSub e1 e2) env = inferArith Lambda.Sub e1 e2 env
infer (RMul e1 e2) env = inferArith Lambda.Mul e1 e2 env
infer (RDiv e1 e2) env = inferArith Lambda.Div e1 e2 env

inferArith ::
  (forall w. Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt) ->
  RawExpr ->
  RawExpr ->
  Map String (UKExpr v γ) ->
  Maybe (UKExpr v γ)
inferArith op e1 e2 env = do
  e1' <- check e1 Lambda.SInt env
  e2' <- check e2 Lambda.SInt env
  Just $ MkUexpr Lambda.SInt (karith op e1' e2')

-- | Check an expression against a known type (checking mode).
check :: RawExpr -> Lambda.STy ty -> Map String (UKExpr v γ) -> Maybe (KExpr v γ ty)
check (RLam x mty e) (Lambda.SArr s1 s2) env = do
  -- If annotated, verify the annotation matches the expected type
  case mty of
    Just ty -> case Lambda.sty ty of
      Lambda.SomeSTy sTy -> case testEquality s1 sTy of
        Just Refl -> pure ()
        Nothing -> Nothing
    Nothing -> pure ()
  e' <- check e s2 (Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env))
  pure $ klam s1 e'
check (RLam _ _ _) _ _ = Nothing -- lambda against non-arrow type
check (RFix x Nothing e) s env = do
  let env' = Map.insert x (MkUexpr s (kvar Here)) (Map.map extendEnv env)
  e' <- check e s env'
  pure $ kfix s e'
check (RNil Nothing) (Lambda.SList s) _env = Just $ knil s
check (RNil Nothing) _ _ = Nothing
check (RLet x Nothing e1 e2) s env = do
  MkUexpr s1 e1' <- infer e1 env
  let env' = Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env)
  e2' <- check e2 s env'
  Just $ kapp (klam s1 e2') e1'
check (RLet x (Just ty) e1 e2) s env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    e1' <- check e1 sTy env
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    e2' <- check e2 s env'
    Just $ kapp (klam sTy e2') e1'
check (RCons e1 e2) (Lambda.SList s) env = do
  e1' <- check e1 s env
  e2' <- check e2 (Lambda.SList s) env
  Just $ kcons e1' e2'
check (RCons _ _) _ _ = Nothing
check e s env = checkInferable e s env -- fallback: infer then compare

checkInferable :: RawExpr -> Lambda.STy ty -> Map String (UKExpr v γ) -> Maybe (KExpr v γ ty)
checkInferable x s env = do
  MkUexpr s' e <- infer x env
  case testEquality s s' of
    Just Refl -> Just e
    Nothing -> Nothing

---------------------------------------------------------------------------
-- Lexer
---------------------------------------------------------------------------

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

reserved :: [String]
reserved = ["Int", "Bool", "List", "fix", "nil", "case", "of", "ifzero", "iszero", "then", "else", "let", "in", "true", "false"]

identifier :: Parser String
identifier = lexeme $ try $ do
  name <- (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_' <|> char '\'')
  if name `elem` reserved
    then fail $ "keyword " ++ show name ++ " is not a valid identifier"
    else pure name

integer :: Parser Int
integer = lexeme L.decimal

---------------------------------------------------------------------------
-- Type parser
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
-- fix (f : Int -> Int). \\(n : Int). ifzero n then 1 else n * f (n - 1)
-- nil \@Int
-- 1 :: 2 :: nil \@Int
-- case xs of { [] -> 0; h :: t -> h }
-- @
parseExpr :: Parser RawExpr
parseExpr = pExpr

pExpr :: Parser RawExpr
pExpr =
  choice
    [ pLam,
      pFix,
      pLet,
      pIfThenElse,
      pCaseList,
      pCons
    ]

pLam :: Parser RawExpr
pLam = do
  _ <- symbol "\\" <|> symbol "λ"
  (x, ty) <-
    parens ((,) <$> identifier <*> optional (symbol ":" *> parseTy))
      <|> (,Nothing)
      <$> identifier
  _ <- symbol "."
  RLam x ty <$> pExpr

pFix :: Parser RawExpr
pFix = do
  _ <- symbol "fix"
  (x, ty) <-
    parens ((,) <$> identifier <*> optional (symbol ":" *> parseTy))
      <|> (,Nothing)
      <$> identifier
  _ <- symbol "."
  RFix x ty <$> pExpr

-- | @let (x : T) = e1 in e2@ or @let x = e1 in e2@
pLet :: Parser RawExpr
pLet = do
  _ <- symbol "let"
  (x, ty) <-
    parens ((,) <$> identifier <*> optional (symbol ":" *> parseTy))
      <|> (,Nothing)
      <$> identifier
  _ <- symbol "="
  e1 <- pExpr
  _ <- symbol "in"
  RLet x ty e1 <$> pExpr

pIfThenElse :: Parser RawExpr
pIfThenElse = do
  _ <- symbol "if"
  e <- pCons
  _ <- symbol "then"
  e1 <- pExpr
  _ <- symbol "else"
  RIfThenElse e e1 <$> pExpr

pCaseList :: Parser RawExpr
pCaseList = do
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
pCons :: Parser RawExpr
pCons = do
  e <- pArith
  rest <- optional (symbol "::")
  case rest of
    Nothing -> pure e
    Just _ -> RCons e <$> pCons

pArith :: Parser RawExpr
pArith =
  makeExprParser
    pUnary
    [ [InfixL (RMul <$ symbol "*"), InfixL (RDiv <$ symbol "/")],
      [InfixL (RAdd <$ symbol "+"), InfixL (RSub <$ symbol "-")]
    ]

pUnary :: Parser RawExpr
pUnary =
  choice
    [ RNeg <$> (symbol "-" *> pUnary),
      RIsZero <$> (symbol "iszero" *> pUnary),
      pApp
    ]

-- left-associative application
pApp :: Parser RawExpr
pApp = foldl1 RApp <$> some pAtom

pAtom :: Parser RawExpr
pAtom =
  choice
    [ RLit <$> integer,
      RBTrue <$ symbol "true",
      RBFalse <$ symbol "false",
      pNil,
      RVar <$> identifier,
      parens pExpr
    ]

pNil :: Parser RawExpr
pNil = do
  _ <- symbol "nil"
  ty <- optional (symbol "@" *> tyAtom)
  pure $ RNil ty

-- | Parse a complete input (skip leading whitespace, expect EOF).
parseModule :: Parser RawExpr
parseModule = sc *> pExpr <* eof

---------------------------------------------------------------------------
-- Compilation pipeline
---------------------------------------------------------------------------

-- | Parse a string as a Lambda expression, typecheck it against @Int -> Int@,
-- and lower it to an arithmetic expression via the presheaf interpretation.
compileIntInt :: String -> Either String (Arith.Expr 'Arith.TInt 'Arith.TInt)
compileIntInt input = do
  raw <- case parse parseModule "" input of
    Left err -> Left (errorBundlePretty err)
    Right r -> Right r
  case check raw (Lambda.SArr Lambda.SInt Lambda.SInt) Map.empty of
    Nothing -> Left "Type error: expression does not have type Int -> Int"
    Just kexpr -> Right $ Lambda.lower (kexpr id Empty)
