module Decidable.Positive.List.Elem

import public Decidable.Positive
import public Decidable.Positive.List.Any

%default total

public export
ELEM : DecEqPos type
    => (x  : type)
    -> (xs : List type)
          -> Decidable
ELEM x xs
  = Any.ANY (DECEQ x) xs

export
isElem : DecEqPos type
      => (x  : type)
      -> (xs : List type)
            -> Positive.Dec (ELEM x xs)
isElem x xs
  = Any.any (decEqPOS x) xs

namespace Exemplar
  public export
  data Elem : (x : type) -> (xs : List type) -> Type where
    H : (prf : Positive (EQ x y))
            -> Elem x (y::xs)

    T : (no    : Negative (EQ x y))
     -> (later : Elem x xs)
              -> Elem x (y::xs)

  export
  Show (Elem x xs) where
    show (H prf)
      = "H"
    show (T no later)
      = "(T \{show later}})"

  public export
  data ElemNot : (x : type) -> (xs : List type) -> Type where
    Empty : ElemNot x Nil
    TNot  : (prf   : Negative (EQ x  y))
         -> (later : ElemNot x     xs)
                  -> ElemNot x (y::xs)

  export
  Show (ElemNot x xs) where
    show (Empty)
      = "{}"
    show (TNot no later)
      = "(TNot \{show later}})"

  prf : Elem    x xs
     -> ElemNot x xs
     -> Void
  prf (H Refl) (TNot no _)
    = no Refl
  prf (T no later) (TNot no' y)
    = prf later y

  public export
  ELEM : (x : type) -> (xs : List type) -> Decidable
  ELEM x xs
    = D (Elem    x xs)
        (ElemNot x xs)
        prf

  export
  elem : DecEq type
      => (x : type)
      -> (xs : List type)
            -> Dec (ELEM x xs)
  elem x []
    = Left Empty
  elem x (y :: xs) with (decEq x y)
    elem x (x :: xs) | (Right Refl)
      = Right (H Refl)
    elem x (y :: xs) | (Left no) with (elem x xs)
      elem x (y :: xs) | (Left no) | (Left z)
        = Left (TNot no z)
      elem x (y :: xs) | (Left no) | (Right z)
        = Right (T no z)

  -- [ EOF ]
