module Decidable.Positive.All.Any

import public Data.List.Quantifiers
import public Decidable.Positive

public export
data Any : (item  : type -> Type)
        -> (pos   : Decidable -> Type)
        -> (neg   : Decidable -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)
        -> (xs    : All item is)
                 -> Type
  where
    Here : {0 p : {i : type} -> (x : item i) -> Decidable}
        -> (  prf : neg (p x))
                 -> Any item pos neg p (x::xs)

    There : {0 p : {i : type} -> (x : item i) -> Decidable}
         -> (  prf : pos (p x))
         -> ( tail : Any item pos neg p xs)
                  -> Any item pos neg p (x::xs)

public export
data All : (item  : type -> Type)
        -> (pos   : Decidable -> Type)
        -> (neg   : Decidable -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)

        -> (xs    : All item is)
                 -> Type
  where
    Empty : {0 p : {i : type} -> (x : item i) -> Decidable}
         -> All item pos neg p Nil

    Extend : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> (  prf : pos (p x))
          -> ( tail : All item pos neg p xs)
                   -> All item pos neg p (x::xs)



public export
0
isVoid : {p : {i : type} -> (x : item i) -> Decidable}
      -> Any item Negative Positive p xs
      -> All item Negative Positive p xs
      -> Void
isVoid {p = p} {xs = (x :: xs)} (Here pP) (Extend pF tail) with (p x)
  isVoid {p = p} {xs = (x :: xs)} (Here pP) (Extend pF tail) | (D pos neg cancelled)
    = cancelled pP pF

isVoid {p = p} {xs = (x :: xs)} (There prf tail) (Extend y z) = isVoid tail z

public export
ANY : (item : type -> Type)
   -> (p    : {i : type} -> (x : item i) -> Decidable)
   -> (xs   : All item is)
           -> Decidable
ANY (item) p xs
  = D (Any item Negative Positive p xs)
      (All item Negative Positive p xs)
      isVoid

--export
--exists : (f  : (x : type) -> Positive.Dec (p x))
--      -> (xs : All item is)
--            -> Positive.Dec (EXISTS p xs)

-- [ EOF ]
