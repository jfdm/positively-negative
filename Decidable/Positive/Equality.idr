module Decidable.Positive.Equality

import public Decidable.Positive

namespace Positive
  public export
  interface DecEq type where
    DECEQpos : (x,y : type) -> Type
    DECEQneg : (x,y : type) -> Type
    0 DECEQprf : {x,y : type} -> DECEQpos x y -> DECEQneg x y -> Void

    DECEQ : (x,y : type) -> Decidable
    DECEQ x y = D (DECEQpos x y) (DECEQneg x y) DECEQprf

    DECEQIN : (x,y : type) -> Decidable
    DECEQIN x y = D (DECEQneg x y) (DECEQpos x y) (\x,y => DECEQprf y x)

    0 DECEQeq  : {x,y : type} ->  DECEQpos x y -> Equal x y
    0 DECEQeqn : {x,y : type} ->  DECEQpos x y -> DECEQneg x y -> Not (Equal x y)

    decEq : (x,y : type)
                -> Positive.Dec (DECEQ x y)

    decEqN : (x,y : type)
                 -> Positive.Dec (DECEQIN x y)

-- [ EOF ]
