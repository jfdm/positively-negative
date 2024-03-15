module Decidable.Positive.List

import public Decidable.Positive

%default total

public export
data IsEmpty : (xs : List a) -> Type where
  Empty : IsEmpty Nil

public export
data IsCons : (xs : List a) -> Type where
  Cons : IsCons (x::xs)

prf : IsEmpty xs -> IsCons xs -> Void
prf Empty Cons impossible

public export
ISEMPTY : (xs : List a) -> Decidable
ISEMPTY xs
  = D (IsEmpty xs)
      (IsCons  xs)
      prf

public export
ISCONS : (xs : List a) -> Decidable
ISCONS
  = (Positive.Not . ISEMPTY)

export
isEmpty : (xs : List a) -> Positive.Dec (ISEMPTY xs)
isEmpty []
  = Right Empty
isEmpty (x :: xs)
  = Left Cons

export
isCons : (xs : List a) -> Positive.Dec (ISCONS xs)
isCons xs = mirror (isEmpty xs)

-- [ EOF ]
