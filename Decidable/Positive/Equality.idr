module Decidable.Positive.Equality

import Decidable.Positive

namespace Positive
  public export
  interface DecEQ type where

    EQUAL : (x,y : type) -> Decidable

    toRefl : {x,y : type}
          -> (EQUAL x y).Positive
          -> Equal x y

    toVoid : {x,y : type}
          -> (EQUAL x y).Negative
          -> Equal x y
          -> Void

    decEq : (x,y : type) -> Positive.Dec (EQUAL x y)

namespace Practical
  export
  decEq' : DecEQ type => (x,y : type) -> Either ((EQUAL x y).Negative) (x = y)
  decEq' x y with (Positive.decEq x y)
    decEq' x y | (Left z) = Left z
    decEq' x y | (Right z) = Right $ toRefl z


-- [ EOF ]
