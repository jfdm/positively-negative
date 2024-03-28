module Decidable.Positive.String

import public Decidable.Positive
import public Decidable.Positive.So
import public Decidable.Positive.Equality

%default total

public export
data AreEqual : (Decidable -> Type) -> (x,y : String) -> Type where
  Same : (prf : t (SO (x == y))) -> AreEqual t x y

void : So x -> Oh x -> Void
void Oh Uh impossible


isVoid : AreEqual Positive x y
      -> AreEqual Negative x y
      -> Void
isVoid (Same p) (Same n)
  = void p n

canRefl : forall x,y
        . AreEqual Positive x y
        -> Equal x y
canRefl (Same prf) = believe_me (Refl {x})


canVoid : forall x,y
        . AreEqual Negative x y
       -> Equal x y
       -> Void
canVoid (Same z) Refl
  = believe_me {b = Void} ()

public export
Positive.DecEq String where
  POS = AreEqual Positive
  NEG = AreEqual Negative

  VOID = isVoid

  toRefl = canRefl
  toVoid = canVoid

  toReflInEq = canRefl
  toVoidInEq = canVoid

  decEq x y with (chooseSO (x == y))
    decEq x y | (Left z)
      = Left (Same z)
    decEq x y | (Right z)
      = Right (Same z)

  decEqN x y = mirror (decEq x y)


-- [ EOF ]
