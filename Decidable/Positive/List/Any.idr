module Decidable.Positive.List.Any

import public Decidable.Positive
import public Decidable.Positive.List.All

%default total

0
prf : {xs  : List type}
   -> Any p Negative Positive xs
   -> All p Negative Positive xs
   -> Void
prf {p} {xs=x::xs} (Here neg) (Extend pos rest) with (p x)
  prf {p = p} {xs=x::xs} (Here neg) (Extend pos rest) | (D positive negative cancelled)
    = cancelled neg pos

prf {p} {xs=x::xs} (There pos rest) (Extend neg later) with (p x)
  prf {p = p} {xs=x::xs} (There pos rest) (Extend neg later) | (D positive negative cancelled) with (Any.prf rest later)
    prf {p = p} {xs=x::xs} (There pos rest) (Extend neg later) | (D positive negative cancelled) | boom
      = boom

export
ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
ANY p xs
  = D (Any     p Negative Positive xs)
      (All     p Negative Positive xs)
      (Any.prf)

export
any : {p  : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ANY p xs)
any f []
  = Left Empty

any {p} f (x :: xs) with (p x)
  any {p = p} f (x :: xs) | (D positive negative cancelled) with (f x)
    any {p = p} f (x :: xs) | (D positive negative cancelled) | res with (polarity' res)
      any {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Left y) with (Any.any f xs)
        any {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Left y) | (Left z) = Left (Extend y z)
        any {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Left y) | (Right z) = Right (There y z)
      any {p = p} f (x :: xs) | (D positive negative cancelled) | res | (Right y) = Right (Here y)

export
showANY : (f : {x : _} -> Positive (p x) -> String)
       -> (g : {x : _} -> Negative (p x) -> String)
       -> Positive.Dec (ANY p xs)
       -> String
showANY f g (Left x) = "(No (All) \{showAll g x})"
showANY f g (Right x) = "(Yes (Any) \{showAny g f x})"

namespace Wrong

  0
  prf : {xs  : List type}
     -> Any p Positive Negative xs
     -> All p Positive Negative xs
     -> Void
  prf x y = All.prf y x

  export
  ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
  ANY p xs
    = D (Any     p Positive Negative xs)
        (All     p Positive Negative xs)
        (Any.Wrong.prf)

  export
  any : {p  : type -> Decidable}
     -> (f  : (x : type) -> Positive.Dec (p x))
     -> (xs : List type)
           -> Positive.Dec (Wrong.ANY p xs)
  any f xs with (All.all f xs)
    any f xs | (Left x)
      = Right x
    any f xs | (Right x)
      = Left x

  export
  showANY : (f : {x : _} -> Positive (p x) -> String)
         -> (g : {x : _} -> Negative (p x) -> String)
         -> Positive.Dec (Wrong.ANY p xs)
         -> String
  showANY f g (Left x) = "(No (All) \{showAll f x})"
  showANY f g (Right x) = "(Yes (Any) \{showAny f g x})"


-- [ EOF ]
