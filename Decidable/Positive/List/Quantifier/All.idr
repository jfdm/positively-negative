module Decidable.Positive.List.Quantifier.All

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier.Core

%default total


public export
0
prf : {xs  : List type}
   -> All p Positive Negative xs
   -> Any p Positive Negative xs
   -> Void
prf Empty (Here x) impossible
prf Empty (There x rest) impossible

prf {p} {xs=(x::xs)} (Extend pos rest) any with (any)
  prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (Here neg) with (p x)
    prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (Here neg) | (D positive negative cancelled)
      = cancelled pos neg
  prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (There pos' later) with (All.prf rest later)
    prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (There pos' later) | boom
      = boom


public export
ALL : (p : type -> Decidable) -> (xs : List type) -> Decidable
ALL p xs
  = D (All     p Positive Negative xs)
      (Any     p Positive Negative xs)
      (All.prf)

export
all : (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ALL p xs)
all f []
  = Right Empty

all {p} f (x :: xs) with (decideE (f x))
  all {p = p} f (x :: xs) | (Left y)
    = Left (Here y)
  all {p = p} f (x :: xs) | (Right y) with (All.all f xs)
    all {p = p} f (x :: xs) | (Right y) | (Left z) = Left (There y z)
    all {p = p} f (x :: xs) | (Right y) | (Right z) = Right (Extend y z)

--  = decidableE (f x)
--               (Left . Here)
--               (\prf => decidable (All.all f xs) ?a ?b)

--  all {p = p} f (x :: xs) | (D positive negative cancelled) with (f x)
--    all {p = p} f (x :: xs) | (D positive negative cancelled) | hres with (All.all f xs)
--      all {p = p} f (x :: xs) | (D positive negative cancelled) | hres | (Left y)
--        = decidable (Left . Here) (\x => Left $ There x y) hres
--
--      all {p = p} f (x :: xs) | (D positive negative cancelled) | hres | (Right y)
--        = decidable (Left . Here) (\x => Right (Extend x y)) hres

--with 0 (p x)
--  all {p = p} f (x :: xs) | (D pos neg _) with (f x)
--    all {p = p} f (x :: xs) | (D pos neg _) | res with (polarity res)
--      all {p = p} f (x :: xs) | (D pos neg prf) | (Left s) | IN = ?as_rhs_0_rhs_rhs
--      all {p = p} f (x :: xs) | (D pos neg prf) | (Right v) | IP = ?as_rhs_0_rhs_rha

--all f []
--  = Right Empty
--
--all {p} f (x :: xs) with (p x)
--  all {p = p} f (x :: xs) | (D positive negative cancelled) with (f x)
--    all {p = p} f (x :: xs) | (D positive negative cancelled) | res with (polarity' res)
--      all {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Left y) = Left (Here y)
--      all {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Right y) with (All.all f xs)
--        all {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Right y) | (Left z)
--          = Left (There y z)
--        all {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Right y) | (Right z)
--          = Right (Extend y z)

export
showALL : (f : {x:_} -> Positive (p x) -> String)
       -> (g : {x:_} -> Negative (p x) -> String)
       -> Positive.Dec (ALL p xs)
       -> String
showALL f g (Left x)
  = "(No (Any) \{showAny f g x})"
showALL f g (Right x)
  = "(Yes (All) \{showAll f x})"

-- [ EOF ]
