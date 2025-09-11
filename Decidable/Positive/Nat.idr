||| Decidable things for Natural numbers.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Nat

import public Data.Nat

import        Decidable.Positive
import public Decidable.Positive.Equality

%default total

||| Helper predicate to ensure that Nats are non-zero.
|||
public export
data IsZero : Nat -> Type where
  ItIsZero : IsZero Z


public export
ISZERO : Nat -> Decidable
ISZERO n
  = D (IsZero n) (IsSucc n) prf
  where
  prf : forall n . IsZero n -> IsSucc n -> Void
  prf ItIsZero ItIsSucc impossible

export
isZero : (n : Nat) -> Dec (ISZERO n)
isZero 0
  = Right ItIsZero
isZero (S k)
  = Left ItIsSucc

public export
ISSUCC : Nat -> Decidable
ISSUCC
  = (Swap . ISZERO)

export
isSucc : (n : Nat) -> Dec (ISSUCC n)
isSucc n = mirror (isZero n)

||| Helper instance...
export
[Helper] {x,y : Nat} -> Show (Nat.LTE x y) where
  show {x} {y} _ = "(\{show x} <= \{show y})"


public export
GT : (x,y : Nat) -> Decidable
GT x y
  = D (GT  x y)
      (LTE x y)
      prf
  where

  prf : forall x, y
      . GT  x y
     -> LTE x y
     -> Void
  prf (LTESucc z) (LTESucc w)
    = prf z w

export
isGT : (x,y : Nat) -> Positive.Dec (GT x y)
isGT 0        0  = Left LTEZero
isGT 0     (S k) = Left LTEZero
isGT (S k)    0  = Right (LTESucc LTEZero)
isGT (S k) (S j)
  = either (Left  . LTESucc)
           (Right . LTESucc)
           (isGT k j)

public export
LTE : (x,y : Nat) -> Decidable
LTE x y
  = Swap (GT x y)

export
isLTE : (x,y : Nat) -> Positive.Dec (LTE x y)
isLTE x y = mirror (isGT x y)

public export
LT : (x,y : Nat) -> Decidable
LT x y
  = D (LT  x y)
      (GTE x y)
      prf

  where
  prf : forall x, y
      . LT  x y
     -> GTE x y
     -> Void
  prf (LTESucc z) (LTESucc w)
    = prf z w


export
isLT : (x,y : Nat) -> Positive.Dec (LT x y)
isLT Z        Z  = Left LTEZero
isLT Z     (S k) = Right (LTESucc LTEZero)
isLT (S k)    Z  = Left LTEZero

isLT (S k) (S j)
  = either (Left  . LTESucc)
           (Right . LTESucc)
           (isLT k j)

public export
GTE : (x,y : Nat) -> Decidable
GTE x y
  = Swap (LT x y)

export
isGTE : (x,y : Nat) -> Positive.Dec (GTE x y)
isGTE x y = mirror (isLT x y)

public export
data AreEqual : (x,y : Nat) -> Type where
  Zero : AreEqual Z Z
  Succ : AreEqual x y -> AreEqual (S x) (S y)

public export
data AreEqualNot : (x,y : Nat) -> Type where
  MoreLeft  : AreEqualNot (S x)    Z
  MoreRight : AreEqualNot    Z  (S y)
  MoreBoth  : AreEqualNot    x     y
           -> AreEqualNot (S x) (S y)


toRefl : AreEqual x y -> Equal x y
toRefl Zero = Refl
toRefl (Succ z) with (toRefl z)
  toRefl (Succ z) | Refl = Refl

toVoid : AreEqualNot x y -> Equal x y -> Void
toVoid (MoreBoth z) Refl with (toVoid z)
  toVoid (MoreBoth z) Refl | no = no Refl

public export
DecEQ Nat where
  EQUAL x y = D (AreEqual x y) (AreEqualNot x y) doCancel
    where
    doCancel : forall x, y
             . AreEqual x y
            -> AreEqualNot x y
            -> Void
    doCancel Zero MoreLeft impossible
    doCancel Zero MoreRight impossible
    doCancel Zero (MoreBoth z) impossible

    doCancel (Succ z) (MoreBoth w) = doCancel z w


  toRefl = Nat.toRefl
  toVoid = Nat.toVoid

  decEq 0 0
    = Right Zero
  decEq 0 (S k)
    = Left MoreRight
  decEq (S k) 0
    = Left MoreLeft
  decEq (S k) (S j)
    = do prf <- (decEq k j) `otherwise` MoreBoth
         pure (Succ prf)

  refl    Z  = Zero
  refl (S k) = Succ $ refl k

-- [ EOF ]
