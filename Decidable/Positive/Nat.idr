module Decidable.Positive.Nat

import public Data.Nat

import public Decidable.Positive

%default total

public export
data IsZero : Nat -> Type where
  ItIsZero : IsZero Z

namespace IsZero

  prf : IsZero n -> IsSucc n -> Void
  prf ItIsZero ItIsSucc impossible

  public export
  ISZERO : Nat -> Decidable
  ISZERO n
    = D (IsZero n) (IsSucc n) prf

  export
  isZero : (n : Nat) -> Positive.Dec (ISZERO n)
  isZero 0
    = Right ItIsZero
  isZero (S k)
    = Left ItIsSucc

namespace IsSucc

  public export
  ISSUCC : Nat -> Decidable
  ISSUCC n
    = D (IsSucc n) (IsZero n) (negSym (Cancelled (ISZERO n)))

  export
  isSucc : (n : Nat) -> Positive.Dec (ISSUCC n)
  isSucc n with (IsZero.isZero n)
    isSucc n | (Left x) = Right x
    isSucc n | (Right x) = Left x

export
{x,y : Nat} -> Show (Nat.LTE x y) where
  show {x} {y} _ = "(\{show x} <= \{show y})"

namespace GreaterThan

  prf : GT  x y
     -> LTE x y
     -> Void
  prf (LTESucc z) (LTESucc w)
    = prf z w

  public export
  GT : (x,y : Nat) -> Decidable
  GT x y
    = D (GT  x y)
        (LTE x y)
        prf

  export
  isGT : (x,y : Nat) -> Positive.Dec (GT x y)
  isGT 0 0 = Left LTEZero
  isGT 0 (S k) = Left LTEZero
  isGT (S k) 0 = Right (LTESucc LTEZero)
  isGT (S k) (S j) with (GreaterThan.isGT k j)
    isGT (S k) (S j) | (Left x) = Left (LTESucc x)
    isGT (S k) (S j) | (Right x) = Right (LTESucc x)


-- [ EOF ]
