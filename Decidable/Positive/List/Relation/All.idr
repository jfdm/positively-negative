module Decidable.Positive.List.Relation.All

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier

%default total

namespace Relation
  public export
  data All : (pred : (x,y : type) -> Decidable)
          -> (xs   : List type)
                  -> Type
    where
      Empty : All p Nil
      Cons  : {x : type}
           -> { 0 p : (x,y : type) -> Decidable}
           -> (head : Positive (ALL (p x) xs))
           -> (tail : All p     xs)
                   -> All p (x::xs)

  public export
  data AllNot : (pred : (x,y : type) -> Decidable)
             -> (xs   : List type)
                     -> Type
    where
      Here : {x : type}
          -> {0 p : (x,y : type) -> Decidable}
          -> (prf : Negative (ALL (p x) xs))
                 -> AllNot p (x::xs)
      There : {x : type}
           -> { 0 p : (x,y : type) -> Decidable}
           -> (head : Positive (ALL (p x) xs))
           -> (tail : AllNot p     xs)
                   -> AllNot p (x::xs)

  0
  prf : All    p xs
     -> AllNot p xs
     -> Void
  prf Empty (Here x) impossible
  prf Empty (There head tail) impossible

  prf {xs = (x::xs)} (Cons hy _) (Here hn)
    = (ALL (p x) xs).Cancelled hy hn
  prf (Cons _ ty)  (There _ tn)
    = prf ty tn

  public export
  ALL : (p  : (x,y : type) -> Decidable)
     -> (xs : List type)
           -> Decidable
  ALL p xs
    = D (All    p xs)
        (AllNot p xs)
        (All.Relation.prf)

  public export
  ALLNOT : (p  : (x,y : type) -> Decidable)
        -> (xs : List type)
              -> Decidable
  ALLNOT p xs
    = Swap (ALL p xs)

  export
  all : (f  : (x,y : type) -> Positive.Dec (p x y))
          -> (xs : List type)
                -> Positive.Dec (Relation.ALL p xs)
  all f []
    = Right Empty
  all f (x :: xs)
    = either (Left . Here)
             (\prfH => either (Left  . There prfH)
                              (Right . Cons prfH)
                              (Relation.all f xs))
             (all (f x) xs)

  export
  any : (f  : (x,y : type) -> Positive.Dec (p x y))
           -> (xs : List type)
                 -> Positive.Dec (Relation.ALLNOT p xs)
  any f xs = mirror (all f xs)

public export
SAMEEQ : DecEQ type => (xs : List type)
    -> Decidable
SAMEEQ  = ALL EQUAL

export
sameByEQ : DecEQ a => (xs : List a) -> Positive.Dec (SAMEEQ xs)
sameByEQ = all decEq

public export
ANYDIFFEQ : DecEQ type
      => (xs : List type)
            -> Decidable
ANYDIFFEQ xs = Swap (SAMEEQ xs)

export
anyDiffByEQ : DecEQ a => (xs : List a) -> Positive.Dec (ANYDIFFEQ xs)
anyDiffByEQ xs = mirror (sameByEQ xs)

public export
FRESHEQ : DecEQ a => (xs : List a) -> Decidable
FRESHEQ = ALL EQUALNOT

export
freshByEQ : DecEQ a => (xs : List a) -> Positive.Dec (FRESHEQ xs)
freshByEQ xs = all decEqNot xs

public export
ANYSAMEEQ : DecEQ a => (xs : List a) -> Decidable
ANYSAMEEQ xs = Swap (FRESHEQ xs)

export
anySameByEQ : DecEQ a => (xs : List a) -> Positive.Dec (ANYSAMEEQ xs)
anySameByEQ xs = mirror (freshByEQ xs)

-- [ EOF ]
