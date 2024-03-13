module Decidable.Positive.Nat

import public Data.Nat

import public Decidable.Positive

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
  urghA (Succ z) (MoreBoth w) Refl with (urghA z w)
    urghA (Succ z) (MoreBoth w) Refl | with_pat = with_pat Refl


  EQUAL : (x,y : Nat) -> Decidable
  EQUAL x y
    = D (AreEqual    x y)
        (AreEqualNot x y)
        prf

  EQUALNOT : (x,y : Nat) -> Decidable
  EQUALNOT x y
    = D (AreEqualNot x y)
        (AreEqual    x y)
        (\x,y => prf y x)

  equal : (x,y : Nat) -> Positive.Dec (EQUAL x y)
  equal Z Z
    = Right Zero
  equal Z (S k)
    = Left MoreRight
  equal (S k) Z
    = Left MoreLeft
  equal (S k) (S j) with (equal k j)
    equal (S k) (S j) | (Left x)
      = Left (MoreBoth x)
    equal (S k) (S j) | (Right x)
      = Right (Succ x)

  equalNot : (x,y : Nat) -> Positive.Dec (EQUALNOT x y)
  equalNot Z Z
    = Left Zero
  equalNot Z (S k)
    = Right MoreRight
  equalNot (S k) Z
    = Right MoreLeft
  equalNot (S k) (S j) with (equalNot k j)
    equalNot (S k) (S j) | (Left x)
      = Left (Succ x)
    equalNot (S k) (S j) | (Right x)
      = Right (MoreBoth x)

  export
  DecEqPos Nat where
    DECEQpos = AreEqual
    DECEQneg = AreEqualNot

    DECEQprf = prf

    DECEQeq  = urgh
    DECEQeqn = urghA
    decEqPOS = equal
    decEqPOSNot = equalNot

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
