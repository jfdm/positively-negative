module Decidable.Positive.List.HasLength

import        Decidable.Positive
import public Data.List.HasLength

%default total

namespace List
  public export
  data HasLengthNot : (n  : Nat)
                   -> (xs : List a)
                         -> Type
    where
      MoreElems : HasLengthNot Z     (x::xs)
      MoreSize  : HasLengthNot (S n) Nil
      Step : HasLengthNot n         xs
          -> HasLengthNot (S n) (x::xs)


prfHasLengthVoid : HasLength    n xs
                -> HasLengthNot n xs
                -> Void
prfHasLengthVoid Z MoreElems impossible
prfHasLengthVoid Z MoreSize impossible
prfHasLengthVoid Z (Step x) impossible

prfHasLengthVoid (S x) (Step y)
  = prfHasLengthVoid x y

public export
HASLENGTH : (n  : Nat)
         -> (xs : List a)
               -> Decidable
HASLENGTH n xs
  = D (HasLength    n xs)
      (HasLengthNot n xs)
      (prfHasLengthVoid)

export
hasLength : (n : Nat) -> (xs : List a) -> Positive.Dec (HASLENGTH n xs)
hasLength 0 []
  = Right Z
hasLength 0 (x :: xs)
  = Left MoreElems
hasLength (S k) []
  = Left MoreSize
hasLength (S k) (x :: xs)
  = either (Left . Step)
           (Right . S)
           (hasLength k xs)

public export
HASLENGTHNOT : (n  : Nat)
            -> (xs : List a)
                  -> Decidable
HASLENGTHNOT n xs
  = D (HasLengthNot n xs)
      (HasLength    n xs)
      (\x,y => prfHasLengthVoid y x)

export
hasLengthNot : (n : Nat) -> (xs : List a) -> Positive.Dec (HASLENGTHNOT n xs)
hasLengthNot n xs
  = mirror (hasLength n xs)


  -- [ EOF ]
