module Decidable.Positive.List.Quantifier.All

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier.Core

%default total

namespace Quantify
  public export
  0
  prf : {xs  : List type}
     -> All p Positive Negative xs
     -> Any p Negative Positive xs
     -> Void
  prf Empty (Here x) impossible
  prf Empty (There x rest) impossible

  prf {p} {xs=(x::xs)} (Extend pos rest) any with (any)
    prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (Here neg)
      = (p x).Cancelled pos neg
    prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (There pos' later)
      = Quantify.prf rest later


  public export
  ALL : (p : type -> Decidable) -> (xs : List type) -> Decidable
  ALL p xs
    = D (All     p Positive Negative xs)
        (Any     p Negative Positive xs)
        (Quantify.prf)

  export
  all : (f  : (x : type) -> Positive.Dec (p x))
     -> (xs : List type)
           -> Positive.Dec (ALL p xs)
  all f []
    = Right Empty

  all {p} f (x :: xs)
    = either (Left . Here)
             (\noH => either (Left  . There noH)
                             (Right . Extend noH)
                             (Quantify.all f xs))
             (f x)
  export
  showALL : (f : {x:_} -> Positive (p x) -> String)
         -> (g : {x:_} -> Negative (p x) -> String)
         -> Positive.Dec (ALL p xs)
         -> String
  showALL f g (Left x)
    = "(No (Any) \{showAny g f x})"
  showALL f g (Right x)
    = "(Yes (All) \{showAll f x})"

-- [ EOF ]
