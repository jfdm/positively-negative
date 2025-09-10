module Decidable.Positive.List.ElemAt

import Decidable.Positive

%default total

namespace List
  public export
  data HoldsAt : (p  : type -> Decidable)
              -> (xs : List type)
              -> (n  : Nat)
                    -> Type
    where
      Here : {0 p   : type -> Decidable}
          -> {0 x   : type}
          -> (  prf : Positive (p x))
                   -> HoldsAt p (x::xs) Z
      There : HoldsAt p     xs     n
           -> HoldsAt p (x::xs) (S n)

  public export
  data HoldsAtNot : (p  : type -> Decidable)
                 -> (xs : List type)
                 -> (n  : Nat)
                       -> Type
    where
      E : HoldsAtNot p Nil n
      H : {0 p   : type -> Decidable}
       -> {0 x   : type}
       -> (  prf : Positive  (p  x))
                -> HoldsAtNot p (x::xs) Z
      T : HoldsAtNot p     xs     n
       -> HoldsAtNot p (x::xs) (S n)

  public export
  0
  isVoid : HoldsAt            p  xs n
        -> HoldsAtNot (Swap . p) xs n
        -> Void
  isVoid {xs = x :: xs} (Here pH) (H pN)
    = (p x).Cancelled pH pN

  isVoid (There ltrY) (T ltrN)
    = isVoid ltrY ltrN

  public export
  HOLDSAT : (p  : type -> Decidable)
         -> (xs : List type)
         -> (n  : Nat)
               -> Decidable
  HOLDSAT p xs n
    = D (HoldsAt            p  xs n)
        (HoldsAtNot (Swap . p) xs n)
        isVoid

  public export
  HOLDSATNOT : (p  : type -> Decidable)
            -> (xs : List type)
            -> (n  : Nat)
                  -> Decidable
  HOLDSATNOT p xs n
    = Swap (HOLDSAT p xs n)

  export
  holdsAt : (f : (x : type) -> Positive.Dec (p x))
         -> (xs : List type)
         -> (n  : Nat)
               -> Positive.Dec (HOLDSAT p xs n)
  holdsAt f [] n
    = Left E
  holdsAt f (x :: xs) Z
    = either (Left . H)
             (Right . Here)
             (f x)

  holdsAt f (x :: xs) (S k)
    = either (Left  . T)
             (Right . There)
             (holdsAt f xs k)

  export
  holdsAtNot : (f  : (x : type) -> Positive.Dec (p x))
            -> (xs : List type)
            -> (n  : Nat)
                  -> Positive.Dec (HOLDSATNOT p xs n)
  holdsAtNot f xs n
    = mirror (holdsAt f xs n)

-- [ EOF ]
