||| SImply decidable things about lists.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.List

import        Decidable.Positive
import public Decidable.Positive.Equality

%default total

public export
data IsEmpty : (xs : List a) -> Type where
  Empty : IsEmpty Nil

public export
data IsCons : (xs : List a) -> Type where
  Cons : IsCons (x::xs)

public export
ISEMPTY : (xs : List a) -> Decidable
ISEMPTY xs
  = D (IsEmpty xs)
      (IsCons  xs)
      prf
  where

  prf : forall xs . IsEmpty xs -> IsCons xs -> Void
  prf Empty Cons impossible

public export
ISCONS : (xs : List a) -> Decidable
ISCONS
  = (Swap . ISEMPTY)

export
isEmpty : (xs : List a) -> Dec (ISEMPTY xs)
isEmpty []
  = Right Empty
isEmpty (x :: xs)
  = Left Cons

export
isCons : (xs : List a) -> Dec (ISCONS xs)
isCons xs = mirror (isEmpty xs)

-- [ EOF ]
