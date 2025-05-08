module Decidable.Positive.List.AtIndex

import public Decidable.Positive
import public Decidable.Positive.Equality



public export
data AtIndex : (x   :      type)
            -> (xs  : List type)
            -> (idx : Nat)
                   -> Type
  where
    Here : AtIndex x (x::xs) Z
    There : (later : AtIndex x     rest     idx)
                  -> AtIndex x (y::rest) (S idx)
