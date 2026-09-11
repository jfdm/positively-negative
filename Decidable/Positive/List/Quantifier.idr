||| Decidable quantifiers for lists.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.List.Quantifier

import public Decidable.Positive

%default total

public export
data All : (pred : (value : type) -> Decidable)
        -> (xs   : List type)
                -> Type
  where
    Empty : All p Nil
    Extend : forall p
           . {x : type}
          -> (prf  : Positive (p x))
          -> (rest : All p     xs)
                  -> All p (x::xs)


public export
data Any : (pred : (value : type) -> Decidable)
        -> (xs   : List type)
                -> Type
  where
    Here : forall p
         . {x    : type}
        -> (prf : Positive (p x))
               -> Any p (x::xs)

    There : forall p
          . {x    : type}
         -> (prf : Negative (p x))
         -> (rest : Any p     xs)
                 -> Any p (x::xs)

0
prf : All p xs
   -> Any (Swap . p) xs
   -> Void
prf Empty (Here x) impossible
prf Empty (There x rest) impossible
prf (Extend pos rest) (Here neg)
  = (p _).Cancels pos neg
prf (Extend pos rest) (There neg ltr)
  = prf rest ltr

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
all f (x :: xs)
  = do pH <- (f x) `otherwise` Here
       pT <- (all f xs) `otherwise` (There pH)
       pure (Extend pH pT)

public export
ANY : (p  : type -> Decidable)
   -> (xs : List type)
         -> Decidable
ANY p xs = Swap (ALL (Swap . p) xs)

export
any : {0 p : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ANY p xs)
any f xs = mirror (all (\x => mirror $ f x) xs)


export
showAll : (f : {x : type} -> Positive (p x) -> String)
       -> Positive (ALL p xs)
       -> String
showAll f Empty
  = "[]"

showAll f (Extend prf rest)
  = "(\{f prf} :: \{showAll f rest})"

export
showAny : (f : {x : type} -> Positive (p x) -> String)
       -> (g : {x : type} -> Negative (p x) -> String)
       -> Any p xs
       -> String
showAny f g (Here prf)
  = f prf
showAny f g (There prf rest)
  = "(\{g prf} :: \{showAny f g rest})"

export
showALL : (f : {x:_} -> Positive (p x) -> String)
       -> (g : {x:_} -> Negative (p x) -> String)
       -> Positive.Dec (ALL p xs)
       -> String
showALL f g (Left x)
  = "(No (Any) \{showAny g f x})"
showALL f g (Right x)
  = "(Yes (All) \{showAll f x})"

export
showANY : (f : {x : _} -> Positive (p x) -> String)
       -> (g : {x : _} -> Negative (p x) -> String)
       -> Positive.Dec (ANY p xs)
       -> String
showANY f g (Left x) = "(No (All) \{showAll g x})"
showANY f g (Right x) = "(Yes (Any) \{showAny f g x})"

-- [ EOF ]
