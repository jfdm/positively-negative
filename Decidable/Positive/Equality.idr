module Decidable.Positive.Equality

import Decidable.Positive

namespace Positive
  public export
  interface DecEQ type where

    EQUAL : (x,y : type) -> Decidable

    EQUALNOT : (x,y : type) -> Decidable
    EQUALNOT x y = Swap (EQUAL x y)


    toRefl : {x,y : type}
          -> (EQUAL x y).Positive
          -> Equal x y

    toVoid : {x,y : type}
          -> (EQUAL x y).Negative
          -> Equal x y
          -> Void

    decEq    : (x,y : type) -> Positive.Dec (EQUAL    x y)
    decEqNot : (x,y : type) -> Positive.Dec (EQUALNOT x y)

    refl : (x : type) -> Positive (EQUAL x x)



    -- need to return Positive version
namespace Practical
  export
  decEq' : DecEQ type => (x,y : type) -> Either ((EQUAL x y).Negative) (x = y)
  decEq' x y = either Left (Right . toRefl) (Positive.decEq x y)


-- [ EOF ]
