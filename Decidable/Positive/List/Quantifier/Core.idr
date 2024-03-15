module Decidable.Positive.List.Quantifier.Core

import public Decidable.Positive

%default total

public export
data All : (pred : (value : type) -> Decidable)
        -> (pos  : Decidable -> Type)
        -> (neg  : Decidable -> Type)
        -> (xs   : List type)
                -> Type
  where
    Empty : All p pos neg Nil
    Extend : {x    : type}
          -> {0 p  : type -> Decidable}
          -> (prf  : pos (p x))
          -> (rest : All p pos neg     xs)
                  -> All p pos neg (x::xs)

export
showAll : (f : {x : _} -> pos (p x) -> String)
       -> All p pos neg xs
       -> String
showAll f Empty
  = "[]"

showAll f (Extend prf rest)
  = "(\{f prf} :: \{showAll f rest})"

public export
data Any : (pred : (value : type) -> Decidable)
        -> (pos  : Decidable -> Type)
        -> (neg  : Decidable -> Type)
        -> (xs   : List type)
                -> Type
  where
    Here : {x   : type}
        -> (prf : neg (p x))
               -> Any p pos neg (x::xs)

    There : {x : type}
         -> (prf : pos (p x))
         -> (rest : Any p pos neg     xs)
                 -> Any p pos neg (x::xs)

export
showAny : (f : {x : _} -> pos (p x) -> String)
       -> (g : {x : _} -> neg (p x) -> String)
       -> Any p pos neg xs
       -> String
showAny f g (Here prf)
  = g prf
showAny f g (There prf rest)
  = "(\{f prf} :: \{showAny f g rest})"


-- [ EOF ]
