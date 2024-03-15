||| Propositional equality is builtin, and sadly equality cannot be
||| truely positve.
module Decidable.Positive.Equality.Propositional

import public Decidable.Positive


prf : Equal x y -> Not (Equal x y) -> Void
prf Refl no
  = no Refl

public export
EQ : (x,y : type) -> Decidable
EQ x y
  = D (Equal x y)
      (Not (Equal x y))
      prf

public export
interface DecEq type where
  decEq : (x,y : type)
              -> Positive.Dec (EQ x y)


-- [ EOF ]
