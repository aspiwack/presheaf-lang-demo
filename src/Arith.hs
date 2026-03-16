{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Arith where

-- | Types in the arithmetic language
data Ty
  = TInt
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
  Pair :: Expr i a -> Expr i b -> Expr i ('TProd a b)
  Fst :: Expr i ('TProd a b) -> Expr i a
  Snd :: Expr i ('TProd a b) -> Expr i b
  Unit :: Expr i 'TUnit

deriving instance Show (Expr i o)

-- Categorical composition of expressions
compose :: Expr i j -> Expr j k -> Expr i k
compose _e Unit = Unit
compose _e (Lit n) = Lit n
compose e1 (Neg e2) = Neg (compose e1 e2)
compose e1 (Add e2 e3) = Add (compose e1 e2) (compose e1 e3)
compose e1 (Sub e2 e3) = Sub (compose e1 e2) (compose e1 e3)
compose e1 (Mul e2 e3) = Mul (compose e1 e2) (compose e1 e3)
compose e1 (Div e2 e3) = Div (compose e1 e2) (compose e1 e3)
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

-- | Values indexed by their type
data Val (t :: Ty) where
  VInt :: Int -> Val 'TInt
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
