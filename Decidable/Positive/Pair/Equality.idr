||| Decidable things for Pairs.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Pair.Equality

import        Decidable.Positive
import public Decidable.Positive.Equality
import        Decidable.Positive.Pair

%default total

%inline
pairToRefl : {x,i : a}
          -> {y,j : b}
          -> (DecEQ a, DecEQ b)
          => Both (EQ i) (EQ j) (x,y)
          -> Equal (i,j) (x,y)
pairToRefl (B pF pS) with (toRefl pF)
  pairToRefl (B pF pS) | Refl with (toRefl pS)
    pairToRefl (B pF pS) | Refl | Refl = Refl

%inline 0
pairToVoid : {x,i : a}
          -> {y,j : b}
          -> (DecEQ a, DecEQ b)
          => BothNot (Swap . EQ i) (Swap . EQ j) (x,y)
          -> Equal (i,j) (x,y)
          -> Void
pairToVoid (FNot pF) Refl = toVoid pF Refl
pairToVoid (SNot pS) Refl = toVoid pS Refl
pairToVoid (BNot pF pS) Refl = toVoid pF Refl

public export
(DecEQ a, DecEQ b) => DecEQ (a,b) where
   EQUAL (x,y) (i,j)
     = BOTH (EQ x) (EQ y) (i,j)

   toRefl {x = (a, b)} {y = (i, j)} prf = pairToRefl prf
   toVoid {x = (a, b)} {y = (a, b)} neg Refl = pairToVoid neg Refl

   refl (x, y) = B (refl x) (refl y)

   decEq (x, y) (i, j) with (decEq x i)
     decEq (x, y) (i, j) | (Left prfNoF)
       = Left (FNot prfNoF)
     decEq (x, y) (i, j) | (Right prfF) with (decEq y j)
       decEq (x, y) (i, j) | (Right prfF) | (Left prfNoR)
         = Left (SNot prfNoR)
       decEq (x, y) (i, j) | (Right prfF) | (Right prfR) = Right (B prfF prfR)

-- [ EOF ]
