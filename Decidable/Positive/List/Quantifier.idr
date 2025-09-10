module Decidable.Positive.List.Quantifier

import public Decidable.Positive

%default total

public export
data All : (pred : (value : type) -> Decidable)
        -> (xs   : List type)
                -> Type
  where
    Empty : All p Nil
    Extend : {x    : type}
          -> {0 p  : type -> Decidable}
          -> (prf  : Positive (p x))
          -> (rest : All p     xs)
                  -> All p (x::xs)


public export
data Any : (pred : (value : type) -> Decidable)
        -> (xs   : List type)
                -> Type
  where
    Here : {x   : type}
        -> {0 p  : type -> Decidable}
        -> (prf : Positive (p x))
               -> Any p (x::xs)

    There : {x : type}
         -> {0 p  : type -> Decidable}
         -> (prf : Negative (p x))
         -> (rest : Any p     xs)
                 -> Any p (x::xs)

0
prf : {xs : List type}
   -> All p xs
   -> Any (Swap . p) xs
   -> Void
prf Empty (Here x) impossible
prf Empty (There x rest) impossible
prf (Extend pos rest) (Here neg) = (p _).Cancelled pos neg
prf (Extend pos rest) (There neg ltr) = prf rest ltr

public export
ALL : (p  : type -> Decidable)
   -> (xs : List type)
         -> Decidable
ALL p xs = D (All         p  xs)
             (Any (Swap . p) xs)
             prf

export
all : (f  : (x : type) -> Positive.Dec (p x))
     -> (xs : List type)
           -> Positive.Dec (ALL p xs)
all f [] = Right Empty
all f (x :: xs) with (f x)
  all f (x :: xs) | (Left y) = Left (Here y)
  all f (x :: xs) | (Right y) with (all f xs)
    all f (x :: xs) | (Right y) | (Left z) = Left (There y z)
    all f (x :: xs) | (Right y) | (Right z) = Right (Extend y z)

0
prf' : {xs : List type}
   -> Any p xs
   -> All (Swap . p) xs
   -> Void
prf' {xs = (x::xs)} (Here y) (Extend n _)
  = (p x).Cancelled y n

prf' (There _ ly) (Extend _ ln)
  = prf' ly ln

public export
ANY : (p  : type -> Decidable)
   -> (xs : List type)
         -> Decidable
ANY p xs
--  = Swap (ALL (Swap . p) xs)
  = D (Any         p  xs)
      (All (Swap . p) xs)
      (prf')

export
any : {0 p : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ANY p xs)
--any f xs = mirror (all (\x => mirror $ f x) xs)
any f []
  = Left Empty
any f (x :: xs) with (f x)
  any f (x :: xs) | (Left nh) with (any f xs)
    any f (x :: xs) | (Left nh) | (Left nl)
      = Left (Extend nh nl)
    any f (x :: xs) | (Left nh) | (Right y)
      = Right (There nh y)
  any f (x :: xs) | (Right yn)
    = Right (Here yn)


export
showAll : (f : {x : _} -> Positive (p x) -> String)
       -> All p xs
       -> String
showAll f Empty
  = "[]"

showAll f (Extend prf rest)
  = "(\{f prf} :: \{showAll f rest})"

export
showAny : (f : {x : _} -> Positive (p x) -> String)
       -> (g : {x : _} -> Negative (p x) -> String)
       -> Any p xs
       -> String
showAny f g (Here prf)
  = f prf
showAny f g (There prf rest)
  = "(\{g prf} :: \{showAny f g rest})"


-- [ EOF ]
