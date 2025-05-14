module Decidable.Positive.List.AtIndex

import Decidable.Positive

public export
data AtIndex : (x   :      type)
            -> (xs  : List type)
            -> (idx : Nat)
                   -> Type
  where
    Here : AtIndex x (x::xs) Z
    There : (later : AtIndex x     rest     idx)
                  -> AtIndex x (y::rest) (S idx)


-- [ E0F ]
