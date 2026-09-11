||| Decidable things for Natural numbers.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Nat.Equality

import        Decidable.Positive
import public Decidable.Positive.Equality

%default total

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


  toRefl = Equality.toRefl
  toVoid = Equality.toVoid

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
