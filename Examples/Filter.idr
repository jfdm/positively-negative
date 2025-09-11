||| A Filter Example
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Filter

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.List.Quantifier


public export
data Interleaving : (xs, ys, zs : List type) -> Type where
  Empty   : Interleaving Nil Nil Nil

  Left : {xs,ys,zs : List type}
      -> (x : type)
      -> (rest : Interleaving xs ys zs)
              -> Interleaving (x::xs) ys (x::zs)
  Right : {xs,ys,zs : List type}
       -> (y : type)
       -> (rest : Interleaving xs ys zs)
               -> Interleaving xs (y::ys) (y::zs)

public export
data Filter : (holdsFor : type -> Decidable)
           -> (input : List type)
           -> Type
  where
    MkFilter : {thrown : List type}
            -> (kept : List type)
            -> (prfOrdering : Interleaving kept thrown input)
            -> (prfKept     : Positive (ALL holdsFor kept))
            -> (prfThrown   : Positive (ALL (Swap . holdsFor) thrown))
            -> Filter holdsFor input

filter : (test  : (value : type) -> Positive.Dec (holds value))
      -> (input : List type)
               -> Filter holds input
filter test []
  = MkFilter [] Empty Empty Empty

filter test (x :: xs) with (filter test xs)
  filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) with (test x)
    filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) | (Left prf)
      = MkFilter kept (Right x prfOrdering) prfKept (Extend prf prfThrown)
    filter test (x :: xs) | (MkFilter kept prfOrdering prfKept prfThrown) | (Right prf)
      = MkFilter (x::kept) (Left x prfOrdering) (Extend prf prfKept) prfThrown


-- [ EOF ]
