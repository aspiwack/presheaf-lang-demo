{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeAbstractions #-}

-- | Typechecks parsed terms into the intrinsically typed terms of the "Lambda"
-- module. Technically, it does name resolution in the same pass.
--
-- I used a bidirectional typing algorithm, largely with the objective of
-- avoiding unification. The algorithm isn't particularly principled, with many
-- constructions appearing both as inferable and checkable.
--
-- The main interest of this module is that it illustrate how to do a
-- typechecking algorithm with parametric higher-order abstract syntax (PHOAS).
-- Which turned out to be significantly less obvious than I had anticipated.
module Typecheck where

import Data.Kind
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Type.Equality
import Error.Diagnose
import GHC.Exts (WithDict (..))
import Lambda qualified as Lambda
import Parser

---------------------------------------------------------------------------
--
-- De Bruijn encoding
--
---------------------------------------------------------------------------

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

-- | Basically encodes (typed) de Bruijn indices without creating a new type. I
-- wish I could find a source for that trick. It's pretty similar to how
-- environments are used to embed neutral terms in preheaves presentations of
-- normalisation by evaluation (NbE).
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

---------------------------------------------------------------------------
--
-- Type errors
--
---------------------------------------------------------------------------

data TcError = TcError
  { tcPos :: Position,
    tcMessage :: String,
    tcHints :: [String]
  }
  deriving (Show)

showTy :: Lambda.STy ty -> String
showTy = show . Lambda.demoteSTy

---------------------------------------------------------------------------
--
-- Bidirectional typechecker
--
---------------------------------------------------------------------------

-- | Infer the type of an expression (synthesis mode).
infer :: Located RawExpr -> Map String (UKExpr v γ) -> Either TcError (UKExpr v γ)
infer (Located pos (RVar x)) env = case Map.lookup x env of
  Just e -> Right e
  Nothing -> Left $ TcError pos ("variable not in scope: " ++ x) []
infer (Located _pos (RLit n)) _ = Right $ MkUexpr Lambda.SInt (klit n)
infer (Located pos (RLam _ Nothing _)) _ =
  Left $ TcError pos "cannot infer type of unannotated lambda" ["add a type annotation"]
infer (Located _pos (RLam x (Just ty) e)) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    MkUexpr sRes e' <- infer e env'
    Right $ MkUexpr (Lambda.SArr sTy sRes) (klam sTy e')
infer (Located _pos (RLet x Nothing e1 e2)) env = do
  MkUexpr s1 e1' <- infer e1 env
  let env' = Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env)
  MkUexpr s2 e2' <- infer e2 env'
  Right $ MkUexpr s2 (kapp (klam s1 e2') e1')
infer (Located _pos (RLet x (Just ty) e1 e2)) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    e1' <- check e1 sTy env
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    MkUexpr s2 e2' <- infer e2 env'
    Right $ MkUexpr s2 (kapp (klam sTy e2') e1')
infer (Located _pos (RApp e1 e2)) env = do
  e1' <- infer e1 env
  case e1' of
    MkUexpr (Lambda.SArr s1 s2) e1'' -> do
      e2' <- check e2 s1 env
      Right $ MkUexpr s2 (kapp e1'' e2')
    MkUexpr s _ ->
      Left $
        TcError
          (locOf e1)
          ("expected a function type, but got " ++ showTy s)
          []
infer (Located pos (RFix _ Nothing _)) _ =
  Left $ TcError pos "cannot infer type of unannotated fix" ["add a type annotation"]
infer (Located _pos (RFix x (Just ty) e)) env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    e' <- check e sTy env'
    Right $ MkUexpr sTy (kfix sTy e')
infer (Located pos (RNil Nothing)) _ =
  Left $ TcError pos "cannot infer type of unannotated nil" ["add a type annotation, e.g. nil@Int"]
infer (Located _pos (RNil (Just ty))) _ = case Lambda.sty ty of
  Lambda.SomeSTy s -> Right $ MkUexpr (Lambda.SList s) (knil s)
infer (Located _pos (RCons e1 e2)) env = do
  MkUexpr s2 e2' <- infer e2 env
  case s2 of
    Lambda.SList sElem -> do
      e1' <- check e1 sElem env
      Right $ MkUexpr s2 (kcons e1' e2')
    _ ->
      Left $
        TcError
          (locOf e2)
          ("expected a list type, but got " ++ showTy s2)
          []
infer (Located _pos (RCaseList scrut enil hd tl econs)) env = do
  MkUexpr sScrut scrut' <- infer scrut env
  case sScrut of
    Lambda.SList sElem -> do
      MkUexpr sRes enil' <- infer enil env
      let env' =
            Map.insert hd (MkUexpr sElem (kvar Here)) $
              Map.insert tl (MkUexpr (Lambda.SList sElem) (kvar (There Here))) $
                Map.map (extendEnv . extendEnv) env
      econs' <- check econs sRes env'
      Right $ MkUexpr sRes (kcaselist sElem sRes scrut' enil' econs')
    _ ->
      Left $
        TcError
          (locOf scrut)
          ("expected a List in case scrutinee, but got " ++ showTy sScrut)
          []
infer (Located _pos (RIfThenElse e e1 e2)) env = do
  e' <- check e Lambda.SBool env
  MkUexpr s e1' <- infer e1 env
  e2' <- check e2 s env
  Right $ MkUexpr s (kifthenelse s e' e1' e2')
infer (Located _pos RBTrue) _ = Right $ MkUexpr Lambda.SBool kbtrue
infer (Located _pos RBFalse) _ = Right $ MkUexpr Lambda.SBool kbfalse
infer (Located _pos (RIsZero e)) env = do
  e' <- check e Lambda.SInt env
  Right $ MkUexpr Lambda.SBool (kiszero e')
infer (Located _pos (RNeg e)) env = do
  e' <- check e Lambda.SInt env
  Right $ MkUexpr Lambda.SInt (kneg e')
infer (Located _pos (RAdd e1 e2)) env = inferArith Lambda.Add e1 e2 env
infer (Located _pos (RSub e1 e2)) env = inferArith Lambda.Sub e1 e2 env
infer (Located _pos (RMul e1 e2)) env = inferArith Lambda.Mul e1 e2 env
infer (Located _pos (RDiv e1 e2)) env = inferArith Lambda.Div e1 e2 env

inferArith ::
  (forall w. Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt -> Lambda.Expr w 'Lambda.TInt) ->
  Located RawExpr ->
  Located RawExpr ->
  Map String (UKExpr v γ) ->
  Either TcError (UKExpr v γ)
inferArith op e1 e2 env = do
  e1' <- check e1 Lambda.SInt env
  e2' <- check e2 Lambda.SInt env
  Right $ MkUexpr Lambda.SInt (karith op e1' e2')

-- | Check an expression against a known type (checking mode).
check :: Located RawExpr -> Lambda.STy ty -> Map String (UKExpr v γ) -> Either TcError (KExpr v γ ty)
check (Located pos (RLam x mty e)) (Lambda.SArr s1 s2) env = do
  case mty of
    Just ty -> case Lambda.sty ty of
      Lambda.SomeSTy sTy -> case testEquality s1 sTy of
        Just Refl -> pure ()
        Nothing ->
          Left $
            TcError
              pos
              ("type annotation " ++ show ty ++ " does not match expected type " ++ showTy s1)
              []
    Nothing -> pure ()
  e' <- check e s2 (Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env))
  pure $ klam s1 e'
check (Located pos (RLam _ _ _)) s _ =
  Left $ TcError pos ("expected " ++ showTy s ++ ", but got a lambda") []
check (Located _pos (RFix x Nothing e)) s env = do
  let env' = Map.insert x (MkUexpr s (kvar Here)) (Map.map extendEnv env)
  e' <- check e s env'
  pure $ kfix s e'
check (Located _pos (RNil Nothing)) (Lambda.SList s) _env = Right $ knil s
check (Located pos (RNil Nothing)) s _ =
  Left $ TcError pos ("expected " ++ showTy s ++ ", but got nil (a list)") []
check (Located _pos (RLet x Nothing e1 e2)) s env = do
  MkUexpr s1 e1' <- infer e1 env
  let env' = Map.insert x (MkUexpr s1 (kvar Here)) (Map.map extendEnv env)
  e2' <- check e2 s env'
  Right $ kapp (klam s1 e2') e1'
check (Located _pos (RLet x (Just ty) e1 e2)) s env = case Lambda.sty ty of
  Lambda.SomeSTy sTy -> do
    e1' <- check e1 sTy env
    let env' = Map.insert x (MkUexpr sTy (kvar Here)) (Map.map extendEnv env)
    e2' <- check e2 s env'
    Right $ kapp (klam sTy e2') e1'
check (Located _pos (RCons e1 e2)) (Lambda.SList s) env = do
  e1' <- check e1 s env
  e2' <- check e2 (Lambda.SList s) env
  Right $ kcons e1' e2'
check (Located pos (RCons _ _)) s _ =
  Left $ TcError pos ("expected " ++ showTy s ++ ", but got a cons expression") []
check (Located _pos (RCaseList scrut enil hd tl econs)) s env = do
  MkUexpr sScrut scrut' <- infer scrut env
  case sScrut of
    Lambda.SList sElem -> do
      enil' <- check enil s env
      let env' =
            Map.insert hd (MkUexpr sElem (kvar Here)) $
              Map.insert tl (MkUexpr (Lambda.SList sElem) (kvar (There Here))) $
                Map.map (extendEnv . extendEnv) env
      econs' <- check econs s env'
      Right $ kcaselist sElem s scrut' enil' econs'
    _ -> Left $ TcError (locOf scrut) ("expected a List in case scrutinee, but got " ++ showTy sScrut) []
check le s env = checkInferable le s env

checkInferable :: Located RawExpr -> Lambda.STy ty -> Map String (UKExpr v γ) -> Either TcError (KExpr v γ ty)
checkInferable le s env = do
  MkUexpr s' e <- infer le env
  case testEquality s s' of
    Just Refl -> Right e
    Nothing ->
      Left $
        TcError
          (locOf le)
          ("expected " ++ showTy s ++ ", but got " ++ showTy s')
          []

---------------------------------------------------------------------------
--
-- Error rendering
--
---------------------------------------------------------------------------

tcErrorToDiagnostic :: FilePath -> String -> TcError -> Diagnostic String
tcErrorToDiagnostic filename source (TcError pos msg hints_) =
  addReport (addFile mempty filename source) $
    Err Nothing msg [(pos, This msg)] (map Hint hints_)
