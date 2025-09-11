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

0
prf' : {xs : List type}
   -> Any p xs
   -> All (Swap . p) xs
   -> Void
prf' {xs = (x::xs)} (Here y) (Extend n _)
  = (p x).Cancels y n

prf' (There _ ly) (Extend _ ln)
  = prf' ly ln

public export
ANY : (p  : type -> Decidable)
   -> (xs : List type)
         -> Decidable
ANY p xs
  = D (Any         p  xs)
      (All (Swap . p) xs)
      (prf')

-- [ NOTE ]
--
-- The nicer version has been removed as idris' elaborator
-- cannot go deep enough and resolve the swaps..

--  = Swap (ALL (Swap . p) xs)

export
any : {0 p : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ANY p xs)
any f []
  = Left Empty
any f (x :: xs)
  = mirror
  $ do nH <- (f x) `wiseother` Here
       nT <- (Quantifier.any f xs) `wiseother` (There nH)
       pure (Extend nH nT)

-- [ NOTE ]
--
-- ibid

--any f xs = mirror (all (\x => mirror $ f x) xs)


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
