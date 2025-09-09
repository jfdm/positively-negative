module Decidable.Positive.So

import public Data.So
import        Decidable.Positive

%default total

public export
data Oh : Bool -> Type where
  Uh : Oh False


public export
SO : (x : Bool) -> Decidable
SO x
  = D (So x) (Oh x) prfSo
  where
  prfSo : forall x . So x -> Oh x -> Void
  prfSo Oh Uh impossible

public export
OH : (x : Bool) -> Decidable
OH = (Swap . SO)

export
isTrue : (b : Bool) -> Positive.Dec (SO b)
isTrue False = Left Uh
isTrue True  = Right Oh

export
isFalse : (b : Bool) -> Positive.Dec (OH b)
isFalse b = mirror (isTrue b)

-- [ EOF ]
