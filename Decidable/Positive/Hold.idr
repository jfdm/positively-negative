module Decidable.Positive.Hold

import Decidable.Positive
import Decidable.Positive.Equality

import Decidable.Positive.Nat

data Holds : (p : type -> Decidable)
          -> (x : type)
               -> Type
  where
    H : {0 p : type -> Decidable}
     -> (prf : Positive (p x))
            -> Holds     p x

data HoldsNot : (p : type -> Decidable)
             -> (x : type)
                  -> Type
  where
    HN : {0 p : type -> Decidable}
      -> (prf : Negative (p x))
             -> HoldsNot  p x

0
prf : Holds p x -> HoldsNot p x -> Void
prf (H y) (HN z) = (p _).Cancelled y z

HOLDS : (p : type -> Decidable)
     -> (x : type)
          -> Decidable
HOLDS p x = D (Holds p x) (HoldsNot p x) prf

holds : {0 p : type -> Decidable}
     -> (f : (x : type) -> Dec (p x))
     -> (x : type)
          -> Dec (HOLDS p x)
holds f x
  = either (Left . HN) (Right . H) (f x)


HOLDSNOT : (p : type -> Decidable)
         -> (x : type)
              -> Decidable
HOLDSNOT p = Swap . HOLDS p

holdsNot : {p : type -> Decidable}
        -> (f : (x : type) -> Dec (p x))
        -> (x : type)
             -> Dec (HOLDSNOT p x)
holdsNot f x = mirror $ holds f x
