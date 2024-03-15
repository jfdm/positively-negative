module Decidable.Positive.List.Relation.All

import public Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.List.All
import public Decidable.Positive.List.Any

%default total

public export
data Relation : (pred : (x,y : type) -> Decidable)
          -> (pos  : Decidable -> Type)
          -> (neg  : Decidable -> Type)
          -> (xs   : List type)
                  -> Type
  where
    Empty : Relation p pos neg Nil
    Cons  : {x : type}
         -> { 0 p : (x,y : type) -> Decidable}
         -> (head : pos (ALL (p x) xs))
         -> (tail : Relation p pos neg xs)
                 -> Relation p pos neg (x::xs)

public export
data RelationNot : (pred : (x,y : type) -> Decidable)
             -> (pos  : Decidable -> Type)
             -> (neg  : Decidable -> Type)
             -> (xs   : List type)
                     -> Type
  where
    Here : {x : type}
        -> {0 p : (x,y : type) -> Decidable}
        -> (prf : neg (ALL (p x) xs))
               -> RelationNot p pos neg (x::xs)
    There : {x : type}
         -> { 0 p : (x,y : type) -> Decidable}
         -> (head : pos (ALL (p x) xs))
         -> (tail : RelationNot p pos neg xs)
                 -> RelationNot p pos neg (x::xs)

0
prf : Relation    p Positive Negative xs
   -> RelationNot p Positive Negative xs
   -> Void
prf Empty (Here x) impossible
prf Empty (There head tail) impossible

prf (Cons hF tF) (Here x)
  = All.prf hF x
prf (Cons _ tF) (There _ tFN)
  = prf tF tFN

public export
RELATION : (p : (x,y : type) -> Decidable)
        -> (xs : List type)
        -> Decidable
RELATION p xs
  = D (Relation    p Positive Negative xs)
      (RelationNot p Positive Negative xs)
      (Relation.prf)

export
relation : (f  : (x,y : type) -> Positive.Dec (p x y))
        -> (xs : List type)
              -> Positive.Dec (RELATION p xs)
relation f []
  = Right Empty
relation f (x :: xs) with (All.all (f x) xs)
  relation f (x :: xs) | (Left y)
    = Left (Here y)
  relation f (x :: xs) | (Right y) with (relation f xs)
    relation f (x :: xs) | (Right y) | (Left z) = Left (There y z)
    relation f (x :: xs) | (Right y) | (Right z) = Right (Cons y z)

public export
FRESHEQ : Positive.DecEq a => (xs : List a) -> Decidable
FRESHEQ = RELATION DECEQIN

export
freshByEQ : Positive.DecEq a => (xs : List a) -> Positive.Dec (FRESHEQ xs)
freshByEQ = relation decEqN

public export
SAMEEQ : Positive.DecEq type => (xs : List type)
    -> Decidable
SAMEEQ  = RELATION DECEQ

export
sameByEQ : Positive.DecEq a => (xs : List a) -> Positive.Dec (SAMEEQ xs)
sameByEQ = relation decEq


-- [ EOF ]
