module Decidable.Positive.List.ElemAt

import Decidable.Positive

%default total

namespace List
  public export
  data HoldsAt : (t  : Decidable -> Type)
              -> (p  : type -> Decidable)
              -> (xs : List type)
              -> (n  : Nat)
                    -> Type
    where
      Here : {0 p   : type -> Decidable}
          -> {0 x   : type}
          -> (  prf : t (p x))
                   -> HoldsAt t p (x::xs) Z
      There : HoldsAt t p     xs     n
           -> HoldsAt t p (x::xs) (S n)

  public export
  data HoldsAtNot : (t  : Decidable -> Type)
                 -> (p  : type -> Decidable)
                 -> (xs : List type)
                 -> (n  : Nat)
                       -> Type
    where
      E : HoldsAtNot t p Nil n
      H : {0 p   : type -> Decidable}
       -> {0 x   : type}
       -> (  prf : t (p x))
                -> HoldsAtNot t p (x::xs) Z
      T : HoldsAtNot t p     xs    n
       -> HoldsAtNot t p (x::xs) (S n)

  public export
  0
  isVoid : HoldsAt    Positive p xs n
        -> HoldsAtNot Negative p xs n
        -> Void
  isVoid {p = p} {xs = (x :: xs)} {n = 0} (Here prfP) (H prfN)
    = (p x).Cancelled prfP prfN

  isVoid {p = p} {xs = (x :: xs)} {n = (S n)} (There lP) (T lN)
    = isVoid lP lN


  public export
  HOLDSAT : (p  : type -> Decidable)
         -> (xs : List type)
         -> (n  : Nat)
               -> Decidable
  HOLDSAT p xs n
    = D (HoldsAt    Positive p xs n)
        (HoldsAtNot Negative p xs n)
        isVoid

  export
  holdsAt : (f : (x : type) -> Positive.Dec (p x))
         -> (xs : List type)
         -> (n  : Nat)
               -> Positive.Dec (HOLDSAT p xs n)
  holdsAt f [] Z
    = Left E

  holdsAt f (x :: xs) Z
    = either (Left . H)
             (Right . Here)
             (f x)

  holdsAt f [] (S k)
    = Left E

  holdsAt f (x :: xs) (S k)
    = either (Left . T)
             (Right . There)
             (holdsAt f xs k)

-- [ EOF ]
