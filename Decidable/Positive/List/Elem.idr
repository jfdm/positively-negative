module Decidable.Positive.List.Elem

import public Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier.Any

%default total

public export
ELEM : Positive.DecEq type
    => (x  : type)
    -> (xs : List type)
          -> Decidable
ELEM x xs
  = Quantify.ANY (DECEQ x) xs

export
isElem : Positive.DecEq type
      => (x  : type)
      -> (xs : List type)
            -> Positive.Dec (ELEM x xs)
isElem x xs
  = Quantify.any (decEq x) xs

  -- [ EOF ]
