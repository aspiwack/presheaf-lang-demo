{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

module Lambda where

import Arith qualified
import Data.Kind
import Data.Type.Equality
import Presheaf
import Sheaf

---------------------------------------------------------------------------
--
-- Syntax
--
---------------------------------------------------------------------------

-- | Types
data Ty
  = TInt -- Int
  | TBool -- Bool
  | TList Ty -- List τ
  | TArr Ty Ty -- τ → σ
  deriving (Eq)

infixr 4 `TArr`

instance Show Ty where
  showsPrec _ TInt = showString "Int"
  showsPrec _ TBool = showString "Bool"
  showsPrec p (TList τ) =
    showParen (p > 10) $
      showString "List " . showsPrec 11 τ
  showsPrec p (TArr τ σ) =
    showParen (p > 4) $
      showsPrec 5 τ . showString " -> " . showsPrec 4 σ

-- | Singletons for 'Ty'
data STy :: Ty -> Type where
  SInt :: STy 'TInt
  SBool :: STy 'TBool
  SList :: STy τ -> STy (TList τ)
  SArr :: STy τ -> STy σ -> STy (TArr τ σ)

instance TestEquality STy where
  testEquality SInt SInt = Just Refl
  testEquality SBool SBool = Just Refl
  testEquality (SList s1) (SList s2) = do
    Refl <- testEquality s1 s2
    Just Refl
  testEquality (SArr s1 s2) (SArr s3 s4) = do
    Refl <- testEquality s1 s3
    Refl <- testEquality s2 s4
    Just Refl
  testEquality _ _ = Nothing

class KnownTy (τ :: Ty) where
  tyRepr :: STy τ

instance KnownTy 'TInt where
  tyRepr = SInt

instance KnownTy 'TBool where
  tyRepr = SBool

instance (KnownTy τ) => KnownTy (TList τ) where
  tyRepr = SList tyRepr

instance (KnownTy τ, KnownTy σ) => KnownTy (TArr τ σ) where
  tyRepr = SArr tyRepr tyRepr

data SomeSTy where
  SomeSTy :: STy τ -> SomeSTy

sty :: Ty -> SomeSTy
sty TInt = SomeSTy SInt
sty TBool = SomeSTy SBool
sty (TList τ) = case sty τ of
  SomeSTy s -> SomeSTy (SList s)
sty (TArr τ σ) = case (sty τ, sty σ) of
  (SomeSTy sτ, SomeSTy sσ) -> SomeSTy (SArr sτ sσ)

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
  CaseList :: (KnownTy σ, KnownTy τ) => Expr v ('TList σ) -> Expr v τ -> (forall w. (forall ρ. (KnownTy ρ) => v ρ -> w ρ) -> w σ -> w ('TList σ) -> Expr w τ) -> Expr v τ
  BTrue :: Expr v 'TBool
  BFalse :: Expr v 'TBool
  IsZero :: Expr v 'TInt -> Expr v 'TBool
  IfThenElse :: (KnownTy τ) => Expr v 'TBool -> Expr v τ -> Expr v τ -> Expr v τ
  Neg :: Expr v 'TInt -> Expr v 'TInt
  Add :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Sub :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Mul :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt
  Div :: Expr v 'TInt -> Expr v 'TInt -> Expr v 'TInt

hoistExpr :: (forall ρ. v ρ -> w ρ) -> Expr v ty -> Expr w ty
hoistExpr k (Var v) = Var (k v)
hoistExpr _ (Lit n) = Lit n
hoistExpr k (Lam s f) = Lam s $ \k' x -> f (k' . k) x
hoistExpr k (App e1 e2) = App (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (Fix s f) = Fix s $ \k' x -> f (k' . k) x
hoistExpr _ (Nil s) = Nil s
hoistExpr k (Cons e1 e2) = Cons (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (CaseList scrut enil econs) =
  CaseList (hoistExpr k scrut) (hoistExpr k enil) $ \k' h t -> econs (k' . k) h t
hoistExpr _ BTrue = BTrue
hoistExpr _ BFalse = BFalse
hoistExpr k (IsZero e) = IsZero (hoistExpr k e)
hoistExpr k (IfThenElse e e1 e2) = IfThenElse (hoistExpr k e) (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (Neg e) = Neg (hoistExpr k e)
hoistExpr k (Add e1 e2) = Add (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (Sub e1 e2) = Sub (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (Mul e1 e2) = Mul (hoistExpr k e1) (hoistExpr k e2)
hoistExpr k (Div e1 e2) = Div (hoistExpr k e1) (hoistExpr k e2)

---------------------------------------------------------------------------
-- Type checker
---------------------------------------------------------------------------

-- Expression of an unknown type
data UExpr v where
  MkUexpr :: STy ty -> Expr v ty -> UExpr v

-- Constructors for UExpr
var :: STy τ -> v τ -> UExpr v
var s v = MkUexpr s (Var v)

lit :: Int -> Maybe (UExpr v)
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
--
-- Interpreter
--
---------------------------------------------------------------------------

-- | Because the interpreter is typed, we need an interpretation of each type.
-- We make sure that this interpretation is always a sheaf. See 'sheafOf' and
-- 'presheafOf' below.
type PreshOf :: Ty -> Presh
type family PreshOf a where
  PreshOf 'TInt = Y 'Arith.TInt
  PreshOf 'TBool = Y 'Arith.TBool
  PreshOf (TList τ) = ShList (PreshOf τ)
  PreshOf (TArr τ σ) = PFun (PreshOf τ) (PreshOf σ)

newtype Fiber i τ = MkFiber (PreshOf τ i)

data Dict c where
  Dict :: (c) => Dict c

presheafOf :: forall ty. STy ty -> Dict (Presheaf (PreshOf ty))
presheafOf SInt = Dict
presheafOf SBool = Dict
presheafOf (SList s) = case presheafOf s of
  Dict -> Dict
presheafOf (SArr s1 s2) = case (presheafOf s1, presheafOf s2) of
  (Dict, Dict) -> Dict

sheafOf :: forall ty. STy ty -> Dict (Sheaf (PreshOf ty))
sheafOf SInt = Dict
sheafOf SBool = Dict
sheafOf (SList s) = case sheafOf s of
  Dict -> Dict
sheafOf (SArr s1 s2) = case (sheafOf s1, sheafOf s2) of
  (Dict, Dict) -> Dict

pbFiber :: (KnownTy ty) => Arith.Expr i j -> Fiber j ty -> Fiber i ty
pbFiber @ty f (MkFiber x) = case presheafOf (tyRepr @ty) of
  Dict -> MkFiber (pb f x)

-- | Note that 'Expr', being a datatype with sums, is only a presheaf. But it's
-- alright (like in the sheaf instance for 'PFun') for the domain to be a
-- presheaf, as long as the codomain is a sheaf. Therefore we can use an @Expr
-- (Fiber i)@ as a context, storing the values for the variables directly in the
-- variable spots.
interp :: forall i ty. Expr (Fiber i) ty -> PreshOf ty i
interp (Var (MkFiber v)) = v
interp (Lit n) = MkY (Arith.Lit n)
interp (Lam _s f) = MkPFun $ \k x ->
  interp (f (pbFiber k) (MkFiber x))
interp (App e1 e2) =
  case interp e1 of
    MkPFun f -> f Arith.Id (interp e2)
interp (Fix _s f) =
  let go = interp (f id (MkFiber go))
   in go
interp (Nil _s) = ShNil
interp (Cons e1 e2) = ShCons (interp e1) (interp e2)
interp (CaseList scrut enil econs) =
  go (interp scrut)
  where
    go (ShNil) = interp enil
    go (ShCons h t) = interp (econs id (MkFiber h) (MkFiber t))
    go (ListOracle k o) =
      case sheafOf (tyRepr @ty) of
        Dict ->
          glueOracle k $ \c -> go (o c)
interp BTrue = MkY Arith.BTrue
interp BFalse = MkY Arith.BFalse
interp (IsZero e) =
  case interp e of
    MkY a -> MkY (Arith.IsZero a)
interp @_ (IfThenElse b t f) =
  case sheafOf (tyRepr @ty) of
    Dict ->
      ifThenElseSh (interp b) (interp t) (interp f)
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

-- | Key entry function. Given a function @int -> int@ in the λ-calculus,
-- evaluate to a circuit 'int -> int' in the base category.
--
-- Since products of representables are representable, it could have been a
-- function of a tuple of int to a tuple of int. But it's a little bit more
-- machinery, and I didn't think it was worth it.
lower :: Expr (Fiber 'Arith.TInt) ('TArr 'TInt 'TInt) -> Arith.Expr 'Arith.TInt 'Arith.TInt
lower e = case interp e of
  MkPFun f -> case f (Arith.Id) (MkY (Arith.Id)) of
    MkY e' -> e'
