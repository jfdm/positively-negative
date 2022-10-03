module Decidable.Positive.Nat

import public Data.Nat

import public Decidable.Positive

%default total

export
Show (Nat.LTE x y) where
  show LTEZero = "LZ"
  show (LTESucc z) = "(LS \{show z})"

namespace GreaterThan

  prf : GT  x y
     -> LTE x y
     -> Void
  prf (LTESucc z) (LTESucc w)
    = prf z w

  public export
  GT : (x,y : Nat) -> Decidable
  GT x y
    = D (GT  x y)
        (LTE x y)
        prf

  export
  isGT : (x,y : Nat) -> Positive.Dec (GT x y)
  isGT 0 0 = Left LTEZero
  isGT 0 (S k) = Left LTEZero
  isGT (S k) 0 = Right (LTESucc LTEZero)
  isGT (S k) (S j) with (GreaterThan.isGT k j)
    isGT (S k) (S j) | (Left x) = Left (LTESucc x)
    isGT (S k) (S j) | (Right x) = Right (LTESucc x)


-- [ EOF ]
