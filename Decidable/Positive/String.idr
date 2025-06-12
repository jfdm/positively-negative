module Decidable.Positive.String

import Decidable.Positive
import public Decidable.Positive.So
import        Decidable.Positive.Equality

%default total

public export
data AreEqual : (Decidable -> Type) -> (x,y : String) -> Type where
  Same : {x,y : String} -> (prf : t (SO (x == y))) -> AreEqual t x y

export
void : So x -> Oh x -> Void
void Oh Uh impossible

export
isVoid : AreEqual Positive x y
      -> AreEqual Negative x y
      -> Void
isVoid (Same p) (Same n)
  = void p n

export
canRefl : forall x,y
        . AreEqual Positive x y
        -> Equal x y
canRefl (Same prf) = believe_me (Refl {x})


export
canVoid : forall x,y
        . AreEqual Negative x y
       -> Equal x y
       -> Void
canVoid (Same z) Refl
  = believe_me {b = Void} ()

export
dup : (x : String) -> AreEqual Positive x x
dup x = Same {t=Positive} {x=x} {y=x} (believe_me $ Data.So.Oh)


public export
DecEQ String where
  EQUAL x y = D (AreEqual Positive x y)
                    (AreEqual Negative x y)
                    isVoid
  toRefl = canRefl
  toVoid = canVoid

  decEq x y with (chooseSO (x == y))
    decEq x y | (Left z)
      = Left (Same z)
    decEq x y | (Right z)
      = Right (Same z)

  self = dup


-- [ EOF ]
