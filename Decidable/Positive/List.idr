module Decidable.Positive.List

import Decidable.Positive
import Decidable.Positive.Equality

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

namespace Equality

  public export
  data AreEqual : (p : a -> a -> Decidable) -> List a -> List a -> Type where
    Here : AreEqual p Nil Nil
    There : {0 p : a -> a -> Decidable}
         -> (p x y).Positive
         -> AreEqual p xs ys
         -> AreEqual p (x::xs) (y::ys)

  public export
  data AreEqualNot : (p : a -> a -> Decidable) -> List a -> List a -> Type where
    LeftHeavy  : AreEqualNot p (x::xs) Nil
    RightHeavy : AreEqualNot p Nil     (y::ys)
    RestNot : {0 p : a -> a -> Decidable} -> {x,y : a}
           -> (  p x y).Positive
           -> AreEqualNot p     xs      ys
           -> AreEqualNot p (x::xs) (y::ys)

    HeadNot : {0 p : a -> a -> Decidable}
          ->  { x,y : a}
           -> (p x y).Negative
            -> AreEqualNot p (x::xs) (y::ys)

  0
  prf : DecEQ a => {xs,ys : List a} -> AreEqual EQUAL xs ys -> AreEqualNot EQUAL xs ys -> Void
  prf Here LeftHeavy impossible
  prf Here RightHeavy impossible
  prf Here (RestNot x y) impossible
  prf Here (HeadNot x) impossible

  prf {xs = (x :: xs)} {ys = (y :: ys)} (There pos z) (RestNot w v)
    = prf z v
  prf {xs = (x :: xs)} {ys = (y :: ys)} (There pos z) (HeadNot w)
    = (EQUAL x y).Cancelled pos w

  asRefl : DecEQ a => {xs, ys : List a} -> AreEqual EQUAL xs ys -> Equal xs ys
  asRefl Here = Refl
  asRefl (There x y) with (toRefl x)
    asRefl (There x y) | Refl with (asRefl y)
      asRefl (There x y) | Refl | Refl = Refl

  0
  asVoid : DecEQ a => {xs, ys : List a} -> AreEqualNot EQUAL xs ys -> Equal xs ys -> Void
  asVoid LeftHeavy Refl impossible
  asVoid RightHeavy Refl impossible

  asVoid {xs = (x :: xs)} {ys = (x :: xs)} (RestNot h ltr) Refl with (asVoid ltr Refl)
    asVoid {xs = (x :: xs)} {ys = (x :: xs)} (RestNot h ltr) Refl | boom = boom

  asVoid {xs = (x :: xs)} {ys = (x :: xs)} (HeadNot hnot) Refl with (toVoid hnot)
    asVoid {xs = (x :: xs)} {ys = (x :: xs)} (HeadNot hnot) Refl | boom = boom Refl

  self : DecEQ a => (xs : List a) -> AreEqual EQUAL xs xs
  self [] = Here
  self (x :: xs) = refl x `There` (self xs)


  public export
  DecEQ a => DecEQ (List a) where

    EQUAL x y
      = D (AreEqual    EQUAL x y)
          (AreEqualNot EQUAL x y)
          prf

    toRefl = asRefl
    toVoid = asVoid

    decEq [] []
      = Right Here

    decEq [] (x :: xs)
      = Left RightHeavy

    decEq (x :: xs) []
      = Left LeftHeavy

    decEq (x :: xs) (y :: ys)
       =  either  (Left . HeadNot)
                  (\h => either (Left . RestNot h)
                                (Right . There h)
                                (decEq xs ys))
                  (decEq x y)

    refl = List.Equality.self

-- [ EOF ]
