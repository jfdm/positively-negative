module Decidable.Positive.So

import public Data.So
import        Decidable.Positive

%default total

public export
data Oh : Bool -> Type where
  Uh : Oh False

prfSo : So x -> Oh x -> Void
prfSo Oh Uh impossible

public export
SO : (x : Bool) -> Decidable
SO x
  = D (So x) (Oh x) prfSo

public export
OH : (x : Bool) -> Decidable
OH = (Swap . SO)

export
chooseSO : (b : Bool) -> Positive.Dec (SO b)
chooseSO False = Left Uh
chooseSO True  = Right Oh

export
chooseOH : (b : Bool) -> Positive.Dec (OH b)
chooseOH b = mirror (chooseSO b)

-- [ EOF ]
