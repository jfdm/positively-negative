||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Pair.Order

import Data.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order

import Decidable.Positive.Pair
import Decidable.Positive.Pair.Equality

ordIsRefl : {0 x : a}
         -> {0 y : b}
         -> (DecORD a, DecORD b)
         => Both (LTE x) (LTE y) (x,y)
                -> Equal (x,y) (x,y)
ordIsRefl (B pF pS) with (isRefl pF)
  ordIsRefl (B pF pS) | Refl with (isRefl pS)
    ordIsRefl (B pF pS) | Refl | Refl = Refl

ordIsAntiSym : {0 x,i : a}
            -> {0 y,j : b}
            -> (DecORD a, DecORD b)
            => Both (LTE x) (LTE y) (i,j)
            -> Both (LTE i) (LTE j) (x,y)
            -> Equal (x,y) (i,j)
ordIsAntiSym (B pFA pSA) (B pFB pSB) with (isSymAnti pFA pFB)
  ordIsAntiSym (B pFA pSA) (B pFB pSB) | Refl with (isSymAnti pSA pSB)
    ordIsAntiSym (B pFA pSA) (B pFB pSB) | Refl | Refl = Refl

ordIsTrans : {0 x,i,s : a}
          -> {0 y,j,t : b}
          -> (DecORD a, DecORD b)
          => Both (LTE x) (LTE y) (i,j)
          -> Both (LTE i) (LTE j) (s,t)
          -> Both (LTE x) (LTE y) (s,t)
ordIsTrans (B pFA pSA) (B pFB pSB) with (isTrans pFA pFB)
  ordIsTrans (B pFA pSA) (B pFB pSB) | prfF with (isTrans pSA pSB)
    ordIsTrans (B pFA pSA) (B pFB pSB) | prfF | prfS
      = B prfF prfS

public export
(DecORD a, DecORD b) => DecORD (a,b) where

  LTE (x,y) (i,j)
    = BOTH (LTE x) (LTE y) (i,j)

  isRefl {x = (x, y)} = ordIsRefl

  isSymAnti {x=(x,y)} {y=(i,j)} pL pG = ordIsAntiSym pL pG

  isTrans {x=(x,y)} {y=(s,t)} {z=(i,j)} pA pB = ordIsTrans pA pB

  decLTE (x, y) (i,j) with (decLTE x i)
    decLTE (x, y) (i,j) | (Left fGT)
      = Left (FNot fGT)
    decLTE (x, y) (i,j) | (Right fLT) with (decLTE y j)
      decLTE (x, y) (i,j) | (Right fLT) | (Left sGT)
        = Left (SNot sGT)
      decLTE (x, y) (i,j) | (Right fLT) | (Right sLT)
        = Right (B fLT sLT)

-- [ EOF ]
