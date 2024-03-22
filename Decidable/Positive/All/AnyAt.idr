module Decidable.Positive.All.AnyAt

import public Data.List.Quantifiers
import public Decidable.Positive

public export
data HoldsAt : (item  : type -> Type)
          -> (pos   : Decidable -> Type)
          -> (p     : {i : type} -> (x : item i) -> Decidable)
          -> (xs    : All item is)
          -> (n     : Nat)
                 -> Type
  where
    Here : {0 p : {i : type} -> (x : item i) -> Decidable}
        -> (  prf : pos (p x))
                 -> HoldsAt item pos p (x::xs) Z

    There : {0 p   : {i : type} -> (x : item i) -> Decidable}
         -> ( tail : HoldsAt item pos p xs n)
                  -> HoldsAt item pos p (x::xs) (S n)

public export
data HoldsAtNot : (item  : type -> Type)
        -> (pos   : Decidable -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)
        -> (xs    : All item is)
        -> (n : Nat)
                 -> Type
  where
    Empty : {0 p   : {i : type} -> (x : item i) -> Decidable} -> HoldsAtNot item pos p Nil n
    H : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> (  prf : pos (p x))
          -> HoldsAtNot item pos p (x::xs) Z

    T : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> ( tail : HoldsAtNot item pos p xs n)
                   -> HoldsAtNot item pos p (x::xs) (S n)

0
isVoid : {p   : {i : type} -> (x : item i) -> Decidable}
      -> HoldsAt    item Positive p xs n
      -> HoldsAtNot item Negative p xs n
      -> Void
isVoid {p = p} {xs = (x :: xs)} {n = 0} (Here prf) (H y) with (p x)
  isVoid {p = p} {xs = (x :: xs)} {n = 0} (Here prf) (H y) | (D positive negative cancelled)
    = cancelled prf y
isVoid {p = p} {xs = (x :: xs)} {n = (S n)} (There tail) (T y) = isVoid tail y


public export
HOLDSAT : {item : type -> Type}
       -> (p : {i : type} -> (x : item i) -> Decidable)
       -> (xs : All item is)
       -> (n  : Nat)
             -> Decidable
HOLDSAT p xs n
  = D (HoldsAt    _ Positive p xs n)
      (HoldsAtNot _ Negative p xs n)
      isVoid


export
holdsAt : {is : _} -> {0 item : k -> Type}
       -> {0 p : {i : k} -> (x : item i) -> Decidable} -> (f : {i : k} -> (x : item i) -> Positive.Dec (p x))
       -> (xs : All item is)
       -> (n  : Nat)
             -> Positive.Dec (HOLDSAT p xs n)
holdsAt f [] n
  = Left Empty
holdsAt f (x :: y) 0 with (decideE $ f x)
  holdsAt f (x :: y) 0 | (Left z)
    = Left (H z)
  holdsAt f (x :: y) 0 | (Right z)
    = Right (Here z)

holdsAt f (x :: y) (S j) with (holdsAt f y j)
  holdsAt f (x :: y) (S j) | (Left z) = Left (T z)
  holdsAt f (x :: y) (S j) | (Right z) = Right (There z)

-- [ EOF ]
