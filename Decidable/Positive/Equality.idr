||| Decidable equality but without requiring void at runtime.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Equality

import Decidable.Positive

||| A `Positive` decision about equality.
namespace Positive

  public export
  interface DecEQ type where

    ||| How equality is decided.
    EQUAL : (x,y : type) -> Decidable

    ||| Ensure that we can compute Equality as expected.
    toRefl : {x,y : type}
          -> (EQUAL x y).Positive
          -> Equal x y

    ||| Ensure that we can compute Void as expected.
    0
    toVoid : {x,y : type}
          -> (EQUAL x y).Negative
          -> Equal x y
          -> Void

    ||| Decide if two given values are equal.
    |||
    ||| Returns evidence explaining if the two values are equal or
    ||| not.
    decEq : (x,y : type) -> Positive.Dec (EQUAL x y)

    ||| Values are equal to themselves.
    refl : (x : type) -> Positive (EQUAL x x)

  namespace Not

    ||| How to decide if things are not equal.
    public export
    EQUALNOT : DecEQ type => (x,y : type) -> Decidable
    EQUALNOT x y = Swap (EQUAL x y)

    ||| Decide if two given values are not equal.
    |||
    ||| Returns evidence explaining if the two values are equal or
    ||| not.
    export
    decEqNot : DecEQ type
            => (x,y : type) -> Positive.Dec (EQUALNOT x y)
    decEqNot x y = mirror (decEq x y)

namespace Practical

  ||| Helper function to compute hard evidence that a value equals
  ||| itself.
  export
  reflRefl : DecEQ type
          => (x : type)
          -> (x = x)
  reflRefl x = toRefl $ refl x

  ||| Helper function to compure hard evidence that two values
  ||| are equal, or evidence why they are not equal.
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
