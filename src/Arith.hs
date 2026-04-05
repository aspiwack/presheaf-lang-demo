{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeAbstractions #-}

module Arith where

import Prettyprinter

-- | Types in the arithmetic language
data Ty
  = TInt
  | TBool
  | TProd Ty Ty
  | TUnit
  deriving (Show, Eq)

-- | Expressions: @Expr i o@ is a computation from input type @i@ to output type @o@
data Expr (i :: Ty) (o :: Ty) where
  Lit :: Int -> Expr i 'TInt
  Id :: Expr i i
  Neg :: Expr i 'TInt -> Expr i 'TInt
  Add :: Expr i 'TInt -> Expr i 'TInt -> Expr i 'TInt
  Sub :: Expr i 'TInt -> Expr i 'TInt -> Expr i 'TInt
  Mul :: Expr i 'TInt -> Expr i 'TInt -> Expr i 'TInt
  Div :: Expr i 'TInt -> Expr i 'TInt -> Expr i 'TInt
  BTrue :: Expr i 'TBool
  BFalse :: Expr i 'TBool
  IsZero :: Expr i 'TInt -> Expr i 'TBool
  IfThenElse :: Expr i 'TBool -> Expr i a -> Expr i a -> Expr i a
  Pair :: Expr i a -> Expr i b -> Expr i ('TProd a b)
  Fst :: Expr i ('TProd a b) -> Expr i a
  Snd :: Expr i ('TProd a b) -> Expr i b
  Unit :: Expr i 'TUnit

deriving instance Show (Expr i o)

---------------------------------------------------------------------------
-- Pretty-printing
---------------------------------------------------------------------------

-- | Pretty-print an expression with a maximum depth.
-- Subexpressions beyond the depth limit are replaced with @…@.
prettyExprDepth :: Int -> Expr i o -> Doc ann
prettyExprDepth maxDepth = go 0 maxDepth
  where
    go :: Int -> Int -> Expr i o -> Doc ann
    go _ _ (Lit n) = pretty n
    go _ _ Id = kw "id"
    go _ _ BTrue = kw "true"
    go _ _ BFalse = kw "false"
    go _ _ Unit = kw "()"
    go _ 0 _ = pretty "…"
    go p d (Neg e) = unary p d (kw "negate") e
    go p d (Add e1 e2) = binOp p d 1 (kw "+") e1 e2
    go p d (Sub e1 e2) = binOp p d 1 (kw "-") e1 e2
    go p d (Mul e1 e2) = binOp p d 2 (kw "*") e1 e2
    go p d (Div e1 e2) = binOp p d 2 (kw "/") e1 e2
    go p d (IsZero e) = unary p d (kw "iszero") e
    go p d (IfThenElse c t f) =
      parensIf (p > 0) $
        group $
          nest 2 $
            sep
              [ kw "if" <+> go 0 d' c,
                kw "then" <+> go 0 d' t,
                kw "else" <+> go 0 d' f
              ]
      where
        d' = d - 1
    go p d (Pair e1 e2) =
      parensIf (p > 0) $
        group $
          nest 2 $
            sep
              [ go 0 (d - 1) e1 <> kw ",",
                go 0 (d - 1) e2
              ]
    go p d (Fst e) = unary p d (kw "fst") e
    go p d (Snd e) = unary p d (kw "snd") e

    binOp p d prec op e1 e2 =
      parensIf (p > prec) $
        group $
          nest 2 $
            sep
              [ go prec d' e1 <+> op,
                go (prec + 1) d' e2
              ]
      where
        d' = d - 1

    unary p d name e =
      parensIf (p > 4) $
        group $
          nest 2 $
            sep
              [ name,
                go 5 (d - 1) e
              ]

kw :: String -> Doc ann
kw = pretty

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True = parens
parensIf False = id

-- Categorical composition of expressions
compose :: Expr i j -> Expr j k -> Expr i k
compose _e Unit = Unit
compose _e (Lit n) = Lit n
compose e1 (Neg e2) = Neg (compose e1 e2)
compose e1 (Add e2 e3) = Add (compose e1 e2) (compose e1 e3)
compose e1 (Sub e2 e3) = Sub (compose e1 e2) (compose e1 e3)
compose e1 (Mul e2 e3) = Mul (compose e1 e2) (compose e1 e3)
compose e1 (Div e2 e3) = Div (compose e1 e2) (compose e1 e3)
compose _e BTrue = BTrue
compose _e BFalse = BFalse
compose e1 (IsZero e2) = IsZero (compose e1 e2)
compose e1 (IfThenElse c t f) = IfThenElse (compose e1 c) (compose e1 t) (compose e1 f)
compose e1 (Fst e2) = Fst (compose e1 e2)
compose e1 (Snd e2) = Snd (compose e1 e2)
compose e1 (Pair e2 e3) = Pair (compose e1 e2) (compose e1 e3)
compose e1 Id = e1

-- Some categorical arrows
neg :: Expr 'TInt 'TInt
neg = Neg Id

add :: Expr ('TProd 'TInt 'TInt) 'TInt
add = Add (Fst Id) (Snd Id)

sub :: Expr ('TProd 'TInt 'TInt) 'TInt
sub = Sub (Fst Id) (Snd Id)

mul :: Expr ('TProd 'TInt 'TInt) 'TInt
mul = Mul (Fst Id) (Snd Id)

cdiv :: Expr ('TProd 'TInt 'TInt) 'TInt
cdiv = Div (Fst Id) (Snd Id)

cocone :: Expr 'TUnit a -> Expr 'TUnit a -> Expr 'TBool a
cocone t f = IfThenElse Id (Unit `compose` t) (Unit `compose` f)

-- | Values indexed by their type
data Val (t :: Ty) where
  VInt :: Int -> Val 'TInt
  VBool :: Bool -> Val 'TBool
  VPair :: Val a -> Val b -> Val ('TProd a b)
  VUnit :: Val 'TUnit

deriving instance Show (Val t)

deriving instance Eq (Val t)

-- | Evaluation errors
data EvalError
  = DivisionByZero
  deriving (Show, Eq)

-- | Evaluate an expression given an input value
eval :: Val i -> Expr i o -> Either EvalError (Val o)
eval _ (Lit n) =
  Right (VInt n)
eval v Id =
  Right v
eval v (Neg e) = do
  val <- eval v e
  case val of VInt n -> Right (VInt (negate n))
eval v (Add e1 e2) = do
  val1 <- eval v e1
  val2 <- eval v e2
  case (val1, val2) of (VInt n1, VInt n2) -> Right (VInt (n1 + n2))
eval v (Sub e1 e2) = do
  val1 <- eval v e1
  val2 <- eval v e2
  case (val1, val2) of (VInt n1, VInt n2) -> Right (VInt (n1 - n2))
eval v (Mul e1 e2) = do
  val1 <- eval v e1
  val2 <- eval v e2
  case (val1, val2) of (VInt n1, VInt n2) -> Right (VInt (n1 * n2))
eval v (Div e1 e2) = do
  val1 <- eval v e1
  val2 <- eval v e2
  case (val1, val2) of
    (VInt _, VInt 0) -> Left DivisionByZero
    (VInt n1, VInt n2) -> Right (VInt (n1 `div` n2))
eval _ BTrue = Right (VBool True)
eval _ BFalse = Right (VBool False)
eval v (IsZero e) = do
  val <- eval v e
  case val of VInt n -> Right (VBool (n == 0))
eval v (IfThenElse c t f) = do
  cond <- eval v c
  case cond of
    VBool True -> eval v t
    VBool False -> eval v f
eval v (Pair e1 e2) = do
  v1 <- eval v e1
  v2 <- eval v e2
  Right (VPair v1 v2)
eval v (Fst e) = do
  val <- eval v e
  case val of VPair v1 _ -> Right v1
eval v (Snd e) = do
  val <- eval v e
  case val of VPair _ v2 -> Right v2
eval _v Unit = Right (VUnit)
