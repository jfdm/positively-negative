||| Decidable things for booleans.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Bool.Equality

import        Decidable.Positive
import public Decidable.Positive.Equality

import public Decidable.Positive.Bool

%default total

public export
data AreEqual : (x,y : Bool) -> Type where
  TT : AreEqual True True
  FF : AreEqual False False

public export
data AreEqualNot : (x,y : Bool) -> Type where
  TF : AreEqualNot True False
  FT : AreEqualNot False True

public export
DecEQ Bool where
  EQUAL x y = D (AreEqual x y) (AreEqualNot x y) doCancel
    where
    doCancel : forall x, y
             . AreEqual x y
            -> AreEqualNot x y
            -> Void
    doCancel TT TF impossible
    doCancel TT FT impossible
    doCancel FF TF impossible
    doCancel FF FT impossible

  toRefl TT = Refl
  toRefl FF = Refl

  toVoid TF Refl impossible
  toVoid FT Refl impossible

  decEq False False = Right FF
  decEq False True  = Left FT
  decEq True  False = Left TF
  decEq True  True  = Right TT

  refl False = FF
  refl True  = TT

-- [ EOF ]
