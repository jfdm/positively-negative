module Decidable.Positive.List.Elem

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier
import public Decidable.Positive.List.Quantifier

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

-- [ EOF ]
