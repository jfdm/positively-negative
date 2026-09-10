module Examples.SessionTypes.MPST

import Data.List.Quantifiers

import public Decidable.Positive
import public Decidable.Positive.Dependent
import public Decidable.Positive.Equality
import public Decidable.Positive.String


%default total

data ViewPoint = GLOBAL | LOCAL

data Branch :

data Action : ViewPoint
           -> (rtype,mtype : Type)
           -> (p : (x,y : rtype) -> Decidable)
           -> Type
  where
    Stop : Action k r a p
    Act : (k : O)(src, dest : r)
       -> (prf : Positive (p src dest))
       -> (type : a)
       -> (k    : Action GLOBAL r a p)
               -> Action GLOBAL r a p

    ActL : (opp  : r)
        -> (type : a)
        -> (k    : Action LOCAL r a p)
                -> Action LOCAL r a p
