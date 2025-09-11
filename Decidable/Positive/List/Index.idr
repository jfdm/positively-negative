||| Decidable decisions about list indices.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.List.Index

import Decidable.Positive

%default total

public export
data Index : Nat -> List a -> Type where
  Here : Index Z (x::xs)
  There : Index n xs
       -> Index (S n) (x::xs)

public export
data IndexNot : Nat -> List a -> Type where
  HereN : IndexNot n Nil
  ThereN : IndexNot n xs
       -> IndexNot (S n) (x::xs)

0
prf : Index    n xs
   -> IndexNot n xs
   -> Void
prf Here HereN impossible
prf Here (ThereN x) impossible
prf (There x) (ThereN y)
  = prf x y


public export
INDEX : (n   : Nat)
     -> (idx : List a)
            -> Decidable
INDEX n idx
  = D (Index    n idx)
      (IndexNot n idx)
      prf

export
index : (n   : Nat)
     -> (idx : List a)
            -> Positive.Dec (INDEX n idx)
index 0 (x :: xs)
  = Right Here

index n []
  = Left HereN

index (S k) (x :: xs)
  = either (Left  . ThereN)
           (Right . There)
           (index k xs)

-- [ EOF ]
