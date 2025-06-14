module Decidable.Positive.List.Relation.All

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.Quantifier

%default total

namespace Relation
  public export
  data All : (pred : (x,y : type) -> Decidable)
            -> (pos  : Decidable -> Type)
            -> (neg  : Decidable -> Type)
            -> (xs   : List type)
                    -> Type
    where
      Empty : All p pos neg Nil
      Cons  : {x : type}
           -> { 0 p : (x,y : type) -> Decidable}
           -> (head : pos (ALL (p x) xs))
           -> (tail : All p pos neg xs)
                   -> All p pos neg (x::xs)

  public export
  data AllNot : (pred : (x,y : type) -> Decidable)
               -> (pos  : Decidable -> Type)
               -> (neg  : Decidable -> Type)
               -> (xs   : List type)
                       -> Type
    where
      Here : {x : type}
          -> {0 p : (x,y : type) -> Decidable}
          -> (prf : neg (ALL (p x) xs))
                 -> AllNot p pos neg (x::xs)
      There : {x : type}
           -> { 0 p : (x,y : type) -> Decidable}
           -> (head : pos (ALL (p x) xs))
           -> (tail : AllNot p pos neg xs)
                   -> AllNot p pos neg (x::xs)

  0
  prf : All    p Positive Negative xs
     -> AllNot p Positive Negative xs
     -> Void
  prf Empty (Here x) impossible
  prf Empty (There head tail) impossible

  prf {p} {xs=s::xs} (Cons hF tF) (Here x)
    = All.prf hF x
  prf (Cons _ tF) (There _ tFN)
    = prf tF tFN


  public export
  ALL : (p  : (x,y : type) -> Decidable)
     -> (xs : List type)
           -> Decidable
  ALL p xs
    = D (All    p Positive Negative xs)
        (AllNot p Positive Negative xs)
        (All.Relation.prf)

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
             (All.all (f x) xs)

public export
FRESHEQ : DecEQ a => (xs : List a) -> Decidable
FRESHEQ = ALL (\x,y => Not $ EQUAL x y)

export
freshByEQ : DecEQ a => (xs : List a) -> Positive.Dec (FRESHEQ xs)
freshByEQ = all (\x,y => not $ decEq x y)

public export
SAMEEQ : DecEQ type => (xs : List type)
    -> Decidable
SAMEEQ  = ALL EQUAL

export
sameByEQ : DecEQ a => (xs : List a) -> Positive.Dec (SAMEEQ xs)
sameByEQ = all decEq


-- [ EOF ]
