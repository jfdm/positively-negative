module Decidable.Positive.Hold

import Decidable.Positive
import Decidable.Positive.Equality

import Decidable.Positive.Nat

data Holds : (p   : type -> Decidable)
          -> (x   : type)
               -> Type
  where
    H : {0 p : type -> Decidable}
     -> (prf : Positive (p x))
            -> Holds p x

0
notBoth : Holds         p  x
       -> Holds (Swap . p) x
       -> Void
notBoth (H prfY) (H prfN)
  = (p x).Cancelled prfY prfN

public export
HOLDS : (p : type -> Decidable)
     -> (x : type)
          -> Decidable
HOLDS p x
  = D (Holds         p  x)
      (Holds (Swap . p) x)
      notBoth

public export
HOLDSNOT : (p : type -> Decidable)
        -> (x : type)
             -> Decidable
HOLDSNOT p = Swap . HOLDS p

export
holds : (f : (x : type) -> Positive.Dec (p x))
     -> (x : type)
          -> Dec (HOLDS p x)
holds f x
  = either (Left . H) (Right . H) (f x)

export
holdsNot : (f : (x : type) -> Positive.Dec (p x))
        -> (x : type)
             -> Dec (HOLDSNOT p x)
holdsNot f x
  = mirror (holds f x)

-- [ EOF ]
