module Decidable.Positive.List.Quantifier.Any

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier.Core

%default total

namespace Quantify
  export
  0
  prf : {xs  : List type}
     -> Any p Negative Positive xs
     -> All p Negative Positive xs
     -> Void
  prf {p} {xs=x::xs} (Here neg) (Extend pos rest) with (p x)
    prf {p = p} {xs=x::xs} (Here neg) (Extend pos rest) | (D positive negative cancelled)
      = cancelled neg pos

  prf {p} {xs=x::xs} (There pos rest) (Extend neg later)
    = Quantify.prf rest later


  export
  ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
  ANY p xs
    = D (Any     p Negative Positive xs)
        (All     p Negative Positive xs)
        (Quantify.prf)

  export
  any : {p  : type -> Decidable}
     -> (f  : (x : type) -> Positive.Dec (p x))
     -> (xs : List type)
           -> Positive.Dec (ANY p xs)
  any f []
    = Left Empty

  any f (x :: xs) with (decideE (f x))
    any f (x :: xs) | (Left y) with (Quantify.any f xs)
      any f (x :: xs) | (Left y) | (Left z)
        = Left (Extend y z)
      any f (x :: xs) | (Left y) | (Right z)
        = Right (There y z)
    any f (x :: xs) | (Right y)
      = Right (Here y)

  export
  showANY : (f : {x : _} -> Positive (p x) -> String)
         -> (g : {x : _} -> Negative (p x) -> String)
         -> Positive.Dec (ANY p xs)
         -> String
  showANY f g (Left x) = "(No (All) \{showAll g x})"
  showANY f g (Right x) = "(Yes (Any) \{showAny g f x})"

-- [ EOF ]
