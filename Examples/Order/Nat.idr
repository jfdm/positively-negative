||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Order.Nat

import Data.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order
import Decidable.Positive.Nat

import Examples.Order.Pair

namespace Nat
  natCan : Nat.LTE x y -> Nat.GT x y -> Void
  natCan LTEZero LTEZero impossible
  natCan LTEZero (LTESucc z) impossible
  natCan (LTESucc z) (LTESucc w) with (natCan z w)
    natCan (LTESucc z) (LTESucc w) | with_pat = with_pat

  natRefl : Nat.LTE x x -> x = x
  natRefl LTEZero = Refl
  natRefl (LTESucc y) with (natRefl y)
    natRefl (LTESucc y) | Refl = Refl

  natSymAnti : Nat.LTE x y
            -> Nat.LTE y x
            -> x = y
  natSymAnti LTEZero LTEZero = Refl
  natSymAnti (LTESucc z) (LTESucc w) with (natSymAnti z w)
    natSymAnti (LTESucc z) (LTESucc w) | Refl = Refl


  natTrans : Nat.LTE x y
          -> Nat.LTE   y z
          -> Nat.LTE x   z
  natTrans LTEZero LTEZero = LTEZero
  natTrans LTEZero (LTESucc w) = LTEZero
  natTrans (LTESucc w) (LTESucc v) with (natTrans w v)
    natTrans (LTESucc w) (LTESucc v) | with_pat = LTESucc with_pat

  natLTE : (x,y : Nat) -> Either (GT x y) (LTE x y)
  natLTE 0 0 = Right LTEZero
  natLTE 0 (S k) = Right LTEZero
  natLTE (S k) 0 = Left (LTESucc LTEZero)
  natLTE (S k) (S j) with (natLTE k j)
    natLTE (S k) (S j) | (Left x) = Left (LTESucc x)
    natLTE (S k) (S j) | (Right x) = Right (LTESucc x)


  public export
  DecORD Nat where
    LTE x y = D (LTE x y) (GT x y) natCan
    isRefl = natRefl
    isSymAnti = natSymAnti
    isTrans = natTrans

    decLTE = natLTE

-- [ EOF ]
