module Decidable.Positive.So

import Decidable.Equality

import public Data.So

import public Decidable.Positive

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


prfOh : Oh x -> So x -> Void
prfOh Uh Oh impossible

public export
OH : (x : Bool) -> Decidable
OH = (Positive.Not . SO)

export
chooseSO : (b : Bool) -> Positive.Dec (SO b)
chooseSO False = Left Uh
chooseSO True = Right Oh

export
chooseOH : (b : Bool) -> Positive.Dec (OH b)
chooseOH b = mirror (chooseSO b)

-- [ EOF ]
