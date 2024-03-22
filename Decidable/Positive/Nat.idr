module Decidable.Positive.Nat

import public Data.Nat

import public Decidable.Positive
import public Decidable.Positive.Equality

%default total

namespace AreEqual

  namespace Nat
    public export
    data AreEqual : (x,y : Nat) -> Type where
      Zero : AreEqual Z Z
      Succ : AreEqual x y -> AreEqual (S x) (S y)

  namespace Nat
    public export
    data AreEqualNot : (x,y : Nat) -> Type where
      MoreLeft  : AreEqualNot (S x)    Z
      MoreRight : AreEqualNot    Z  (S y)
      MoreBoth  : AreEqualNot    x     y
               -> AreEqualNot (S x) (S y)


  prf : AreEqual x y -> AreEqualNot x y -> Void
  prf Zero MoreLeft impossible
  prf Zero MoreRight impossible
  prf Zero (MoreBoth z) impossible
  prf (Succ Zero) (MoreBoth MoreLeft) impossible
  prf (Succ Zero) (MoreBoth MoreRight) impossible
  prf (Succ Zero) (MoreBoth (MoreBoth z)) impossible
  prf (Succ (Succ Zero)) (MoreBoth (MoreBoth MoreLeft)) impossible
  prf (Succ (Succ Zero)) (MoreBoth (MoreBoth MoreRight)) impossible
  prf (Succ (Succ Zero)) (MoreBoth (MoreBoth (MoreBoth z))) impossible
  prf (Succ (Succ (Succ z))) (MoreBoth (MoreBoth (MoreBoth w))) = prf z w

  urgh : AreEqual x y -> Equal x y
  urgh Zero = Refl
  urgh (Succ z) with (urgh z)
    urgh (Succ z) | Refl = Refl

  urghA : AreEqual x y -> AreEqualNot x y -> Not (Equal x y)
  urghA Zero MoreLeft Refl impossible
  urghA Zero MoreRight Refl impossible
  urghA Zero (MoreBoth z) Refl impossible
  urghA (Succ z) (MoreBoth w) Refl = urghA z w Refl


  export
  Positive.DecEq Nat where
    DECEQpos = AreEqual
    DECEQneg = AreEqualNot

    DECEQprf = prf

    DECEQeq  = urgh
    DECEQeqn = urghA

    decEq Z Z
      = Right Zero
    decEq Z (S k)
      = Left MoreRight
    decEq (S k) Z
      = Left MoreLeft
    decEq (S k) (S j) with (decEq k j)
      decEq (S k) (S j) | (Left x)
        = Left (MoreBoth x)
      decEq (S k) (S j) | (Right x)
        = Right (Succ x)

    decEqN x y = mirror (decEq x y)

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
  ISSUCC
    = (Positive.Not . ISZERO)

  export
  isSucc : (n : Nat) -> Positive.Dec (ISSUCC n)
  isSucc n = mirror (isZero n)

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


namespace LessThan
  prf : LT  x y
     -> GTE x y
     -> Void
  prf (LTESucc z) (LTESucc w)
    = prf z w

  public export
  LT : (x,y : Nat) -> Decidable
  LT x y
    = D (LT  x y)
        (GTE x y)
        prf

  export
  isLT : (x,y : Nat) -> Positive.Dec (LT x y)
  isLT Z Z
    = Left LTEZero
  isLT Z (S k)
    = Right (LTESucc LTEZero)
  isLT (S k) Z
    = Left LTEZero
  isLT (S k) (S j) with (LessThan.isLT k j)
    isLT (S k) (S j) | (Left x)
      = Left (LTESucc x)
    isLT (S k) (S j) | (Right x)
      = Right (LTESucc x)


-- [ EOF ]
