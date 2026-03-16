{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

module Lambda where

import Arith qualified
import Data.Kind

---------------------------------------------------------------------------
-- Syntax
---------------------------------------------------------------------------

-- | Types
data Ty
  = TInt -- Int
  | TList Ty -- List τ
  | TArr Ty Ty -- τ → σ
  deriving (Eq)

infixr 4 `TArr`

-- | Singletons for 'Ty'
data STy :: Ty -> Type where
  SInt :: STy 'TInt
  SList :: STy τ -> STy (TList τ)
  SArr :: STy τ -> STy σ -> STy (TArr τ σ)

class KnownTy (τ :: Ty) where
  tyRepr :: STy τ

instance KnownTy 'TInt where
  tyRepr = SInt

instance (KnownTy τ) => KnownTy (TList τ) where
  tyRepr = SList tyRepr

instance (KnownTy τ, KnownTy σ) => KnownTy (TArr τ σ) where
  tyRepr = SArr tyRepr tyRepr

instance Show Ty where
  showsPrec _ TInt = showString "Int"
  showsPrec p (TList τ) =
    showParen (p > 10) $
      showString "List " . showsPrec 11 τ
  showsPrec p (TArr τ σ) =
    showParen (p > 4) $
      showsPrec 5 τ . showString " -> " . showsPrec 4 σ

-- | Intrinsically typed expressions in (PHOAS style)
type Expr :: (Ty -> Type) -> Ty -> Type
data Expr v ty where
  Var :: v τ -> Expr v τ
  Lit :: Int -> Expr v 'TInt
  Lam :: STy σ -> (forall w. (forall ρ. (KnownTy ρ) => v ρ -> w ρ) -> w σ -> Expr w τ) -> Expr v ('TArr σ τ)
  App :: Expr v ('TArr σ τ) -> Expr v σ -> Expr v τ
  Fix :: STy τ -> (forall w. (forall ρ. (KnownTy ρ) => v ρ -> w ρ) -> w τ -> Expr w τ) -> Expr v τ
  Nil :: STy τ -> Expr v ('TList τ)
  Cons :: Expr v τ -> Expr v ('TList τ) -> Expr v ('TList τ)
  CaseList :: Expr v ('TList σ) -> Expr v τ -> (v σ -> v ('TList σ) -> Expr v τ) -> Expr v τ
  IfZero :: Expr v 'TInt -> Expr v τ -> Expr v τ -> Expr v τ
  Neg :: Expr v 'TInt -> Expr v 'TInt
  Add :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Sub :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Mul :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Div :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt

---------------------------------------------------------------------------
-- Type checker
---------------------------------------------------------------------------

-- Expression of an unknown type
data UExpr where
  MkUexpr :: STy ty -> Expr v ty -> UExpr

-- Constructors for UExpr
lit :: Int -> Maybe UExpr
lit n = Just (MkUexpr SInt (Lit n))

-- lam :: STy σ -> (v σ -> UExpr) -> Maybe UExpr
-- lam s f = do
--   MkUexpr s' e <- f (undefined :: v σ)
--   if s == s'
--     then Just (MkUexpr (SArr s s') (Lam s (\x -> e)))
--     else Nothing

-- data TyCtx = TyCtx
--   { termVars :: Map TermVar Ty
--   }

-- emptyTyCtx :: TyCtx
-- emptyTyCtx = TyCtx Map.empty

-- data TypeError
--   = UnboundVar TermVar
--   | TypeMismatch Ty Ty -- expected, got
--   | NotAFunction Ty
--   | NotAList Ty
--   | NotAnInt Ty
--   deriving (Show, Eq)

-- -- Primitive types
-- typecheck :: TyCtx -> Expr -> Either TypeError Ty
-- typecheck ctx (Var x) =
--   maybe (Left (UnboundVar x)) Right (Map.lookup x (termVars ctx))
-- typecheck _ (Lit _) = Right TInt
-- typecheck ctx (Lam x τ e) = do
--   let ctx' = ctx {termVars = Map.insert x τ (termVars ctx)}
--   σ <- typecheck ctx' e
--   Right (TArr τ σ)
-- typecheck ctx (App e1 e2) = do
--   τ <- typecheck ctx e1
--   σ <- typecheck ctx e2
--   case τ of
--     TArr τa τb
--       | τa == σ -> Right τb
--       | otherwise -> Left (TypeMismatch τa σ)
--     _ -> Left (NotAFunction τ)
-- typecheck _ (Fix τ) = Right (TArr (TArr τ τ) τ)
-- typecheck _ (Nil τ) = Right (TList τ)
-- typecheck _ (Cons τ) = Right (TArr τ (TArr (TList τ) (TList τ)))
-- typecheck ctx (CaseList scrut enil hd tl econs) = do
--   τ <- typecheck ctx scrut
--   elemTy <- case τ of
--     TList t -> Right t
--     _ -> Left (NotAList τ)
--   τnil <- typecheck ctx enil
--   let ctx' =
--         ctx
--           { termVars =
--               Map.insert hd elemTy (Map.insert tl (TList elemTy) (termVars ctx))
--           }
--   τcons <- typecheck ctx' econs
--   if τnil == τcons
--     then Right τnil
--     else Left (TypeMismatch τnil τcons)
-- typecheck ctx (IfZero e e1 e2) = do
--   τ <- typecheck ctx e
--   τ1 <- typecheck ctx e1
--   τ2 <- typecheck ctx e2
--   case τ of
--     TInt -> pure ()
--     _ -> Left (NotAnInt τ)
--   if τ1 == τ2
--     then Right τ1
--     else Left (TypeMismatch τ1 τ2)
-- typecheck ctx (Neg e) = do
--   τ <- typecheck ctx e
--   case τ of
--     TInt -> Right TInt
--     _ -> Left (NotAnInt τ)
-- typecheck ctx (Add e1 e2) = typecheckArith ctx e1 e2
-- typecheck ctx (Sub e1 e2) = typecheckArith ctx e1 e2
-- typecheck ctx (Mul e1 e2) = typecheckArith ctx e1 e2
-- typecheck ctx (Div e1 e2) = typecheckArith ctx e1 e2

-- typecheckArith :: TyCtx -> Expr -> Expr -> Either TypeError Ty
-- typecheckArith ctx e1 e2 = do
--   τ1 <- typecheck ctx e1
--   τ2 <- typecheck ctx e2
--   case (τ1, τ2) of
--     (TInt, TInt) -> Right TInt
--     (TInt, _) -> Left (NotAnInt τ2)
--     _ -> Left (NotAnInt τ1)

---------------------------------------------------------------------------
-- Interpreter
---------------------------------------------------------------------------

type Presh = Arith.Ty -> Type

class Presheaf (p :: Presh) where
  pb :: Arith.Expr i j -> p j -> p i

type Y :: Arith.Ty -> Presh
newtype Y a i = MkY (Arith.Expr i a)

instance Presheaf (Y a) where
  pb f (MkY e) = MkY (Arith.compose f e)

type PProd :: Presh -> Presh -> Presh
newtype PProd p q i = MkPProd (p i, q i)

instance (Presheaf p, Presheaf q) => Presheaf (PProd p q) where
  pb f (MkPProd (x, y)) = MkPProd (pb f x, pb f y)

type PList :: Presh -> Presh
newtype PList p i = MkPList [p i]

instance (Presheaf p) => Presheaf (PList p) where
  pb f (MkPList xs) = MkPList (map (pb f) xs)

type PFun :: Presh -> Presh -> Presh
newtype PFun p q i = MkPFun (forall j. Arith.Expr j i -> p j -> q j)

instance (Presheaf p, Presheaf q) => Presheaf (PFun p q) where
  pb f (MkPFun g) = MkPFun $ \k x -> g (Arith.compose k f) x

lamP :: (Presheaf p, Presheaf q, Presheaf r) => (forall i. PProd p q i -> r i) -> (forall i. p i -> PFun q r i)
lamP f x = MkPFun $ \k y -> f (MkPProd (pb k x, y))

type PreshOf :: Ty -> Presh
type family PreshOf a where
  PreshOf 'TInt = Y 'Arith.TInt
  PreshOf (TList τ) = PList (PreshOf τ)
  PreshOf (TArr τ σ) = PFun (PreshOf τ) (PreshOf σ)

newtype Fiber i τ = MkFiber (PreshOf τ i)

data Dict c where
  Dict :: (c) => Dict c

presheafOf :: forall ty. STy ty -> Dict (Presheaf (PreshOf ty))
presheafOf SInt = Dict
presheafOf (SList s) = case presheafOf s of
  Dict -> Dict
presheafOf (SArr s1 s2) = case (presheafOf s1, presheafOf s2) of
  (Dict, Dict) -> Dict

pbFiber :: (KnownTy ty) => Arith.Expr i j -> Fiber j ty -> Fiber i ty
pbFiber @ty f (MkFiber x) = case presheafOf (tyRepr @ty) of
  Dict -> MkFiber (pb f x)

interp :: forall ty i. Expr (Fiber i) ty -> PreshOf ty i
interp (Var (MkFiber v)) = v
interp (Lit n) = MkY (Arith.Lit n)
interp (Lam _s f) = MkPFun $ \k x ->
  interp (f (pbFiber k) (MkFiber x))
interp (App e1 e2) =
  case interp e1 of
    MkPFun f -> f Arith.Id (interp e2)
-- fix via lazy knot-tying: the recursive variable points to the result itself
interp (Fix _s f) =
  let go = interp (f (pbFiber Arith.Id) (MkFiber go))
   in go
interp (Nil _s) = MkPList []
interp (Cons e1 e2) =
  case interp e2 of
    MkPList t -> MkPList (interp e1 : t)
interp (CaseList scrut enil econs) =
  case interp scrut of
    MkPList [] -> interp enil
    MkPList (h : t) -> interp (econs (MkFiber h) (MkFiber (MkPList t)))
interp (IfZero _e _e1 _e2) =
  error "IfZero: cannot branch on symbolic arithmetic expressions"
interp (Neg e) =
  case interp e of
    MkY a -> MkY (Arith.Neg a)
interp (Add e1 e2) = interpArith Arith.Add e1 e2
interp (Sub e1 e2) = interpArith Arith.Sub e1 e2
interp (Mul e1 e2) = interpArith Arith.Mul e1 e2
interp (Div e1 e2) = interpArith Arith.Div e1 e2

interpArith ::
  (Arith.Expr i 'Arith.TInt -> Arith.Expr i 'Arith.TInt -> Arith.Expr i 'Arith.TInt) ->
  Expr (Fiber i) 'TInt ->
  Expr (Fiber i) 'TInt ->
  Y 'Arith.TInt i
interpArith op e1 e2 =
  case (interp e1, interp e2) of
    (MkY a1, MkY a2) -> MkY (op a1 a2)

lower :: (forall v. Expr v ('TArr 'TInt 'TInt)) -> Arith.Expr 'Arith.TInt 'Arith.TInt
lower e = case interp e of
  MkPFun f -> case f (Arith.Id) (MkY (Arith.Id)) of
    MkY e' -> e'
