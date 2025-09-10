module Decidable.Positive.All.Any

import public Data.List.Quantifiers
import        Decidable.Positive

public export
data Any : (item  : type -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)
        -> (xs    : All item is)
                 -> Type
  where
    Here : {0 p : {i : type} -> (x : item i) -> Decidable}
        -> (  prf : Positive (p x))
                 -> Any item p (x::xs)

    There : {0 p : {i : type} -> (x : item i) -> Decidable}
         -> (  prf : Negative (p x))
         -> ( tail : Any item p xs)
                  -> Any item p (x::xs)

public export
data All : (item  : type -> Type)
        -> (p     : {i : type} -> (x : item i) -> Decidable)
        -> (xs    : All item is)
                 -> Type
  where
    Empty : {0 p : {i : type} -> (x : item i) -> Decidable}
         -> All item p Nil

    Extend : {0 p   : {i : type} -> (x : item i) -> Decidable}
          -> (  prf : Positive (p x))
          -> ( tail : All item p xs)
                   -> All item p (x::xs)

0
isVoid : {p : {i : type} -> (x : item i) -> Decidable}
      -> Any item         p  xs
      -> All item (Swap . p) xs
      -> Void
isVoid {p = p} {xs = (x :: xs)} (Here pP) (Extend pF tail)
    = (p x).Cancelled pP pF

isVoid {p = p} {xs = (x :: xs)} (There prf tail) (Extend y z)
  = isVoid tail z

public export
ANY : (item : type -> Type)
   -> (p    : {i : type} -> (x : item i) -> Decidable)
   -> (xs   : All item is)
           -> Decidable
ANY (item) p xs
  = D (Any item         p  xs)
      (All item (Swap . p) xs)
      isVoid

public export
ALL : (item : type -> Type)
   -> (p    : {i : type} -> (x : item i) -> Decidable)
   -> (xs   : All item is)
           -> Decidable
ALL (item) p xs
  = Swap (ANY item (Swap . p) xs)

export
any : {0 is : List type}
   -> {0 p : {i : type} -> (x : item i) -> Decidable}
   -> (f  : {0 i : type} -> (x : item i) -> Positive.Dec (p x))
   -> (xs : All item is)
         -> Positive.Dec (ANY item p xs)
any f []
  = Left Empty
any f (x :: y)
  = either (\nH => either (Left  . Extend nH)
                          (Right . There nH)
                          (any f y))
           (Right . Here)
           (f x)

export
all : {0 is : List type}
   -> {0 p : {i : type} -> (x : item i) -> Decidable}
   -> (f  : {0 i : type} -> (x : item i) -> Positive.Dec (p x))
   -> (xs : All item is)
         -> Positive.Dec (ALL item p xs)
all f xs = mirror (any (\x => mirror $ f x) xs)

-- [ EOF ]
