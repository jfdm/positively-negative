module Decidable.Positive.List.Elem

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier.Core
import public Decidable.Positive.List.Quantifier.Any

%default total

public export
ELEM : DecEQ type
    => (x  : type)
    -> (xs : List type)
          -> Decidable
ELEM x xs
  = Quantify.ANY (EQUAL x) xs

export
isElem : DecEQ type
      => (x  : type)
      -> (xs : List type)
            -> Positive.Dec (ELEM x xs)
isElem x xs
  = Quantify.any (decEq x) xs

-- [ EOF ]
