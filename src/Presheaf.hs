{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeFamilies #-}

-- | Defines presheaves over 'Arith.Expr' and their operations
module Presheaf where

import Arith qualified
import Data.Kind

type Presh = Arith.Ty -> Type

-- | A presheaf over the category 'Arith.Expr' is a family of type indexed by
-- 'Arith.Ty' (the objects of the category), equipped with the following
-- restriction function along arrows of 'Arith.Expr'. Note that restriction is a
-- contravariant function.
--
-- Arrows of the category of presheaves are natural transformations @forall i. p
-- i -> q i@.
--
-- A type @p i@ for some @i@ is called the fiber of @p@ as i.
--
-- There are a number of compatibility conditions (such as restrictions
-- distributing over composition). But they can't be represented in Haskell.
class Presheaf (p :: Presh) where
  pb :: Arith.Expr i j -> p j -> p i

-- | The Yoneda embedding. Embeds 'Arith.Expr' (as a full subcategory) in
-- presheaves.
type Y :: Arith.Ty -> Presh
newtype Y a i = MkY (Arith.Expr i a)

unY :: Y a i -> Arith.Expr i a
unY (MkY e) = e

-- | 'yonedaf' and 'yonedab' are two sides of an isomorphism which proves in
-- particular that 'Y' is an embedding.
yonedaf :: (Presheaf p) => (forall i. Y a i -> p i) -> p a
yonedaf f = f (MkY Arith.Id)

-- | See 'yonedaf'
yonedab :: (Presheaf p) => p a -> (forall i. Y a i -> p i)
yonedab x (MkY f) = pb f x

instance Presheaf (Y a) where
  pb f (MkY e) = MkY (Arith.compose f e)

-- | The (categorical) product of two presheaves. It's define fiber-wise.
type PProd :: Presh -> Presh -> Presh
newtype PProd p q i = MkPProd (p i, q i)

instance (Presheaf p, Presheaf q) => Presheaf (PProd p q) where
  pb f (MkPProd (x, y)) = MkPProd (pb f x, pb f y)

fstp :: PProd p q i -> p i
fstp (MkPProd (x, _)) = x

sndp :: PProd p q i -> q i
sndp (MkPProd (_, y)) = y

-- The terminal presheaf. It's define fiber-wise.
type PUnit :: Presh
data PUnit i = MkPUnit

instance Presheaf PUnit where
  pb _ (MkPUnit) = MkPUnit

-- | The coproduct of two presheaves. It's define fiber-wise.
--
-- That sums (=coproducts) are defined fiberwise means that the presheaf
-- category creates all the sums. This means that control flow in the category
-- of presheaves is independent from control flow in the base category. It can
-- be a problem.
type PSum :: Presh -> Presh -> Presh
newtype PSum p q i = MkPSum (Either (p i) (q i))

instance (Presheaf p, Presheaf q) => Presheaf (PSum p q) where
  pb f (MkPSum (Left x)) = MkPSum (Left (pb f x))
  pb f (MkPSum (Right y)) = MkPSum (Right (pb f y))

-- Since sums and products are defined fiber-wise, any data structure is defined
-- fiberwise. Here lists.
type PList :: Presh -> Presh
newtype PList p i = MkPList [p i]

instance (Presheaf p) => Presheaf (PList p) where
  pb f (MkPList xs) = MkPList (map (pb f) xs)

-- | The exponential object of the category of presheaves. This is a crucial
-- definition, which cannot be fiber-wise.
type PFun :: Presh -> Presh -> Presh
newtype PFun p q i = MkPFun (forall j. Arith.Expr j i -> p j -> q j)

runPFun :: PFun p q i -> (forall j. Arith.Expr j i -> p j -> q j)
runPFun (MkPFun f) = f

instance (Presheaf p, Presheaf q) => Presheaf (PFun p q) where
  pb f (MkPFun g) = MkPFun $ \k x -> g (Arith.compose k f) x

-- | For illustration: 'lamP' and 'openLamP' witness the adjunction between 'PProd' and 'PFun'
lamP :: (Presheaf p, Presheaf q, Presheaf r) => (forall i. PProd p q i -> r i) -> (forall i. p i -> PFun q r i)
lamP f x = MkPFun $ \k y -> f (MkPProd (pb k x, y))

-- | See 'lamP'
openLamP :: (Presheaf p, Presheaf q, Presheaf r) => (forall i. p i -> PFun q r i) -> (forall i. PProd p q i -> r i)
openLamP f (MkPProd (x, y)) = runPFun (f x) Arith.Id y
