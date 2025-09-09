module Decidable.Positive.Equality

import Decidable.Positive

namespace Positive
  public export
  interface DecEQ type where

    EQUAL : (x,y : type) -> Decidable

    toRefl : {x,y : type}
          -> (EQUAL x y).Positive
          -> Equal x y

    0
    toVoid : {x,y : type}
          -> (EQUAL x y).Negative
          -> Equal x y
          -> Void

    decEq    : (x,y : type) -> Positive.Dec (EQUAL x y)

    refl : (x : type) -> Positive (EQUAL x x)

  namespace Not

    public export
    EQUALNOT : DecEQ type => (x,y : type) -> Decidable
    EQUALNOT x y = Swap (EQUAL x y)

    export
    decEqNot : DecEQ type
            => (x,y : type) -> Positive.Dec (EQUALNOT x y)
    decEqNot x y = mirror (decEq x y)

namespace Practical

  export
  reflRefl : DecEQ type
          => (x : type)
          -> (x = x)
  reflRefl x = toRefl $ refl x

  export
  decEq' : DecEQ type
          => (x,y : type)
                 -> Either (Negative (EQUAL x y))
                           (x = y)
  decEq' x y
    = either Left
             (Right . toRefl)
             (decEq x y)


-- [ EOF ]
