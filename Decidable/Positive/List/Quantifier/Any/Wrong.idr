module Decidable.Positive.List.Quantifier.Any.Wrong

import public Decidable.Positive
import public Decidable.Positive.List.Quantifier

%default total

export
ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
ANY p xs
  = Swap (ALL p xs)

export
any : {p  : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (Wrong.ANY p xs)
any f xs = mirror (all f xs)

export
showANY : (f : {x : _} -> Positive (p x) -> String)
       -> (g : {x : _} -> Negative (p x) -> String)
       -> Positive.Dec (Wrong.ANY p xs)
       -> String
showANY f g (Left x) = "(No (All) \{showAll f x})"
showANY f g (Right x) = "(Yes (Any) \{showAny g f x})"


-- [ EOF ]
