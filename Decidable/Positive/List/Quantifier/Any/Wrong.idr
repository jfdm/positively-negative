module Decidable.Positive.List.Quantifier.Any.Wrong

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier.Core
import public Decidable.Positive.List.Quantifier.All

%default total

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
      (prf)

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
