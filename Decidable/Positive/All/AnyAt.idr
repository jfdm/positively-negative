||| Decidable things for All List quantifiers.
|||
||| Noticably this design does not track negative things in the
||| `There` constructors.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.All.AnyAt

import Data.List.Quantifiers
import Data.List.AtIndex

import Decidable.Positive
import Decidable.Positive.Dependent


public export
data HoldsAt : (item  : type -> Type)
            -> (p     : {i : type} -> (x : item i) -> Decidable)
            -> (xs    : All item is)
            -> (n     : Nat)
                     -> Type
  where
    Here : {0 p : {i : type} -> (x : item i) -> Decidable}
        -> {i : type}
        -> {x : item i}
        -> (  prf : Positive (p x))
                 -> HoldsAt item p (x::xs) Z

    There : {0 p   : {i : type} -> (x : item i) -> Decidable}
         -> ( tail : HoldsAt item p xs n)
                  -> HoldsAt item p (x::xs) (S n)

public export
data HoldsAtNot : (item  : type -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)
        -> (xs    : All item is)
        -> (n : Nat)
                 -> Type
  where
    Empty : {0 p : {i : type}
         -> (  x : item i) -> Decidable}
                -> HoldsAtNot item p Nil n

    H : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> (  prf : Positive (p x))
          -> HoldsAtNot item p (x::xs) Z

    T : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> ( tail : HoldsAtNot item p xs n)
                   -> HoldsAtNot item p (x::xs) (S n)

0
isVoid : {p   : {i : type} -> (x : item i) -> Decidable}
      -> (n : Nat)
      -> HoldsAt    item         p  xs n
      -> HoldsAtNot item (Swap . p) xs n
      -> Void
isVoid {p = p} {xs = (x :: xs)} 0 (Here prf) (H y)
  = (p x).Cancels prf y
isVoid {p = p} {xs = (x :: xs)} (S n) (There tail) (T y)
  = isVoid n tail y


public export
HOLDSAT : {item : type -> Type}
       -> (p : {i : type} -> (x : item i) -> Decidable)
       -> (xs : All item is)
       -> (n  : Nat)
             -> Decidable
HOLDSAT p xs n
  = D (HoldsAt    _         p xs n)
      (HoldsAtNot _ (Swap . p) xs n)
      (isVoid n)


export
holdsAt : {is : _} -> {0 item : k -> Type}
       -> {0 p : {i : k} -> (x : item i) -> Decidable}
       -> (f : {i : k} -> (x : item i) -> Positive.Dec (p x))
       -> (xs : All item is)
       -> (n  : Nat)
             -> Positive.Dec (HOLDSAT p xs n)
holdsAt f [] n
  = Left Empty

holdsAt f (x :: xs) 0
  = do pH <- f x `otherwise` H
       pure (Here pH)

holdsAt f (x :: xs) (S j)
  = do later <- holdsAt f xs j `otherwise` T
       pure (There later)

namespace Discover

  public export
  HOLDSAT : {item : type -> Type}
         -> (p : {i : type} -> (x : item i) -> Decidable)
         -> (xs : All item is)
               -> DDecidable
  HOLDSAT p xs
    = D Nat (HoldsAt    _         p  xs)
            (HoldsAtNot _ (Swap . p) xs)
            isVoid

  export
  holdsAt : {is : _} -> {0 item : k -> Type}
         -> {0 p : {i : k} -> (x : item i) -> Decidable}
         -> (f : {0 i : k} -> (x : item i) -> Positive.Dec (p x))
         -> (xs : All item is)
               -> Positive.DDec (HOLDSAT p xs)
  holdsAt f []
    = Left (Z ** Empty)
  holdsAt f (x :: xs) with (f x)
    holdsAt f (x :: xs) | (Left nH) with (Discover.holdsAt f xs)
      holdsAt f (x :: xs) | (Left nH) | (Left (idx ** nL))
        = Left (S idx ** T nL)
      holdsAt f (x :: xs) | (Left nH) | (Right (idx ** hL))
        = Right (S idx ** There hL)
    holdsAt f (x :: xs) | (Right yH)
      = Right (0 ** Here yH)


public export
data ToIndex : (item  : type -> Type)
            -> (p     : {i : type} -> (x : item i) -> Decidable)
            -> (xs    : All item is)
            -> (n     : Nat)
                     -> Type
  where
    R :  {0 p : {i : type} -> (x : item i) -> Decidable}
      -> {i : type}
      -> (x : item i)
      -> (prf : Positive $ p x)
      -> { is : All item xs}
      -> AtIndex i xs idx
      -> ToIndex item p is idx

export
toIndex : {is : All item xs}
         -> {0 p : {i : k} -> (x : item i) -> Decidable}
       -> HoldsAt item p is idx
       -> ToIndex item p is idx
toIndex (Here prf) = (R _ prf  Z)
toIndex (There tail) with (toIndex tail)
  toIndex (There tail) | (R _ prf rest)
    = (R _ prf (S rest))

-- [ EOF ]
