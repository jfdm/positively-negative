module Decidable.Positive.List.Quantifier.Any

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier.Core

%default total

namespace Quantify
  export
  0
  prf : {xs  : List type}
     -> Any p Positive Negative xs
     -> All p Negative Positive xs
     -> Void
  prf {p} {xs=x::xs} (Here neg) (Extend pos rest)
    = (p x).Cancelled neg pos

  prf {p} {xs=x::xs} (There pos rest) (Extend neg later)
    = Quantify.prf rest later


  public export
  ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
  ANY p xs
    = D (Any     p Positive Negative xs)
        (All     p Negative Positive xs)
        (Quantify.prf)

  export
  any : (f  : (x : type) -> Positive.Dec (p x))
     -> (xs : List type)
           -> Positive.Dec (ANY p xs)
  any f []
    = Left Empty

  any f (x :: xs)
    = either (\noH => either (Left . Extend noH)
                             (Right . There noH)
                             (Quantify.any f xs))
             (Right . Here)
             (f x)

  export
  showANY : (f : {x : _} -> Positive (p x) -> String)
         -> (g : {x : _} -> Negative (p x) -> String)
         -> Positive.Dec (ANY p xs)
         -> String
  showANY f g (Left x) = "(No (All) \{showAll g x})"
  showANY f g (Right x) = "(Yes (Any) \{showAny f g x})"

-- [ EOF ]
