||| Reasoning about dependent pairs
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.DPair

import Decidable.Equality
import Decidable.Positive

%default total

public export
data OnSecond : (f    : Type)
             -> (s    : (value : f) -> Type)
             -> (pred : {x : f} -> s x -> Decidable)
             -> (pair : DPair f s)
                     -> Type
  where
    Holds : {0 pred : {x : f} -> s x -> Decidable}
         -> {x   : f}
         -> {y   : s x}
         -> (prf : Positive (pred y))
                -> OnSecond f s pred (x ** y)

0
no : {p : {x : f} -> (value : s x) -> Decidable}
  -> OnSecond f s         p  (x ** y)
  -> OnSecond f s (Swap . p) (x ** y)
  -> Void
no (Holds prf) (Holds n) = (p y).Cancels prf n

public export
ONSECOND : (f : Type)
        -> {s : f -> Type}
        -> (p : {x : f} -> s x -> Decidable)
        -> DPair f s
        -> Decidable
ONSECOND f p (x ** y)
  = D (OnSecond f s         p  (x ** y))
      (OnSecond f s (Swap . p) (x ** y))
      no

export
onSecond : {f : Type}
        -> {s : f -> Type}
        -> {p : {x : f} -> s x -> Decidable}
        -> (d : forall x . (value : s x) -> Positive.Dec (p value))
        -> (value : DPair f s)
        -> Positive.Dec (ONSECOND f p value)
onSecond d (fst ** snd)
  = either (Left  . Holds)
           (Right . Holds)
           (d snd)


public export
ONSECONDNOT : (f : Type)
           -> {s : f -> Type}
           -> (p : {x : f} -> s x -> Decidable)
           -> DPair f s
           -> Decidable
ONSECONDNOT f p t
  = Swap (ONSECOND f (Swap . p) t)

export
onSecondNot : {f : Type}
        -> {s : f -> Type}
        -> {p : {x : f} -> s x -> Decidable}
        -> (d : forall x . (value : s x) -> Positive.Dec (p value))
        -> (value : DPair f s)
        -> Positive.Dec (ONSECONDNOT f p value)
onSecondNot d t
  = mirror (onSecond (\x => mirror $ d x) t)
-- [ EOF ]
