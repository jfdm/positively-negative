module Decidable.Positive.Equality

import Decidable.Positive

namespace Positive
  public export
  record DecEqDesc type where
    constructor MkDecEq
    Positive : (x,y : type) -> Type
    Negative : (x,y : type) -> Type
    0 Cancelled : {0 x,y : type}
                        -> Positive x y
                        -> Negative x y
                        -> Void

    toRefl : {0 x,y : type}
                   -> Positive x y
                   -> Equal x y
    toVoid : {0 x,y : type}
                   -> Negative x y
                   -> Equal x y
                   -> Void

  namespace Def
    public export
    DECEQ : (raw : Positive.DecEqDesc type) ->  (x,y : type) -> Decidable
    DECEQ raw x y
      = D (raw.Positive x y)
          (raw.Negative x y)
          (raw.Cancelled)

    public export
    DECEQIN : (raw : Positive.DecEqDesc type) ->  (x,y : type) -> Decidable
    DECEQIN raw x y
      = Swap (DECEQ raw x y)

  public export
  interface DecEq type where
    INST : Positive.DecEqDesc type

    decEq : (x,y : type) -> Positive.Dec (DECEQ INST x y)

    toRefl : forall x, y . (Positive INST) x y -> Equal x y
    toRefl = (toRefl INST)

    toVoid : forall x, y . (Negative INST) x y -> Equal x y -> Void
    toVoid = (toVoid INST)

    decEqN : (x,y : type) -> Positive.Dec (DECEQIN INST x y)
    decEqN x y = mirror (Positive.decEq x y)


  public export
  DECEQ : Positive.DecEq type => (x,y : type) -> Decidable
  DECEQ = DECEQ INST

  public export
  DECEQIN : Positive.DecEq type => (x,y : type) -> Decidable
  DECEQIN = DECEQIN INST

-- [ EOF ]
