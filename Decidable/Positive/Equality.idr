module Decidable.Positive.Equality

import public Decidable.Positive

namespace Positive
  public export
  interface DecEq type where
    POS : (x,y : type) -> Type
    NEG : (x,y : type) -> Type

    0 VOID : {0 x,y : type} -> POS x y -> NEG x y -> Void

    DECEQ : (x,y : type) -> Decidable
    DECEQ x y
      = D (POS x y)
          (NEG x y)
          VOID

    DECEQIN : (x,y : type) -> Decidable
    DECEQIN x y
      = Not (DECEQ x y)

    toRefl : forall x, y . Positive (DECEQ x y) -> Equal x y
    toVoid : forall x, y . Negative (DECEQ x y) -> Equal x y -> Void

    toReflInEq : forall x, y . Negative (DECEQIN x y) -> Equal x y
    toVoidInEq : forall x, y . Positive (DECEQIN x y) -> Equal x y -> Void

    decEq : (x,y : type)
                -> Positive.Dec (DECEQ x y)

    decEqN : (x,y : type)
                 -> Positive.Dec (DECEQIN x y)

  export
  decEqAlt : Positive.DecEq type
          => (x,y : type)
                 -> Dec (Equal x y)
  decEqAlt x y with (decideE $ Positive.decEq x y)
    decEqAlt x y | (Left z) with (toVoid z)
      decEqAlt x y | (Left z) | no = No no
    decEqAlt x y | (Right z) with (Positive.toRefl z)
      decEqAlt x x | (Right z) | Refl = Yes Refl

-- [ EOF ]
