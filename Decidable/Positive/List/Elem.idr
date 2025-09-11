||| Decidable Elem for Lists.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.List.Elem

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier
import public Decidable.Positive.List.HoldsAt

%default total

public export
ELEM : DecEQ type
    => (x  : type)
    -> (xs : List type)
          -> Decidable
ELEM x xs
  = ANY (EQUAL x) xs

export
isElem : DecEQ type
      => (x  : type)
      -> (xs : List type)
            -> Positive.Dec (ELEM x xs)
isElem x xs
  = any (decEq x) xs

public export
ELEMAT : DecEQ type
      => (n  : Nat)
      -> (x  : type)
      -> (xs : List type)
            -> Decidable
ELEMAT n x xs
  = HOLDSAT (EQUAL x) xs n

export
isElemAt : DecEQ type
        => (n  : Nat)
        -> (x  : type)
        -> (xs : List type)
              -> Positive.Dec (ELEMAT n x xs)
isElemAt n x xs
  = holdsAt (decEq x) xs n

-- [ EOF ]
