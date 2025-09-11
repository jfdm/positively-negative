||| Decidable things for runtime Booleans.
|||
||| The decisions here are not informative and mirrors how
||| it is down in Idris for such things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
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
isFalse b = mirror (So.isTrue b)

||| Some times we want things to be blocking.
namespace Blocking
  export
  isTrueBlock : (b : Bool) -> Positive.Dec (SO b)
  isTrueBlock b = case b of
                  False => Left Uh
                  True => Right Oh

  export
  isFalseBlock : (b : Bool) -> Positive.Dec (OH b)
  isFalseBlock b = case b of
                  False => Right Uh
                  True => Left Oh

-- [ EOF ]
