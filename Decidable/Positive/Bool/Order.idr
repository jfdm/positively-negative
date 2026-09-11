||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Bool.Order

import Data.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order

import Decidable.Positive.Bool
import Decidable.Positive.Bool.Equality

%default total

namespace Bool
  public export
  data LTE : (x,y : Bool) -> Type where
    FF : LTE False False
    FT : LTE False True
    TT : LTE True True

  public export
  data GT : (x,y : Bool) -> Type where
    TF : GT True False

%inline 0
prf : Bool.LTE x y -> Bool.GT x y -> Void
prf FF TF impossible
prf FT TF impossible
prf TT TF impossible

public export
DecORD Bool where
  LTE x y = D (LTE x y) (GT x y) prf

  isRefl FF = Refl
  isRefl TT = Refl

  isSymAnti FF FF = Refl
  isSymAnti FT FF impossible
  isSymAnti FT FT impossible
  isSymAnti FT TT impossible
  isSymAnti TT TT = Refl

  isTrans FF FF = FF
  isTrans FF FT = FT
  isTrans FT TT = FT
  isTrans TT TT = TT

  decLTE False False = Right FF
  decLTE False True  = Right FT
  decLTE True  False = Left TF
  decLTE True  True  = Right TT

-- [ EOF ]
