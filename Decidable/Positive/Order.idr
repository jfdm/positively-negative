||| Decidable ordering based on partially ordered sets.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Order

import Decidable.Positive
import Decidable.Positive.Equality

import Data.Nat
import Decidable.Positive.Nat

namespace Postitive
  ||| A Positive Decision about Ordering
  public export
  interface DecEQ type => DecORD type where

      LTE : (x,y : type) -> Decidable

      isRefl : {a   : type}
            -> (prf : (LTE a a).Positive)
                   -> (Equal a a)

      isSymAnti : {a,b : type}
               -> (prfLTE : (LTE a b).Positive)
               -> (prfGTE : (LTE b a).Positive)
                         -> (Equal a b)

      isTrans : {a,b,c : type}
             -> (prfAB : (LTE a b  ).Positive)
             -> (prfBC : (LTE   b c).Positive)
                      -> (LTE a   c).Positive

      decLTE : (x,y : type) -> Positive.Dec (LTE x y)

  public export
  GT : DecORD type => (x,y : type) -> Decidable
  GT x y = Swap (LTE x y)

  public export
  decGT : DecORD type
       => (x,y : type)
              -> Positive.Dec (GT x y)
  decGT x y = mirror (decLTE x y)

  public export
  GTE : DecORD type => (x,y : type) -> Decidable
  GTE x y = (LTE y x)

  public export
  decGTE : DecORD type
       => (x,y : type)
              -> Positive.Dec (GTE x y)
  decGTE x y = decLTE y x

  public export
  LT : DecORD type => (x,y : type) -> Decidable
  LT x y = Swap (LTE y x)

  public export
  decLT : DecORD type
       => (x,y : type)
              -> Positive.Dec (LT x y)
  decLT x y = mirror (decLTE y x)

namespace Compare
  public export
  data Compare : (lt, eq : (x,y : type) -> Decidable)
              -> (a,b : type)
                     -> Type
    where
      LT : forall lt . (prf : (lt a b).Positive) -> Compare lt eq a b
      EQ : forall lt . (prf : (eq a b).Positive) -> Compare lt eq a b
      GT : forall lt . (prf : (lt b a).Positive)  -> Compare lt eq a b

  export
  compare : (DecEQ type, DecORD type) => (x,y : type) -> Compare LT EQ x y
  compare x y with (decLT x y)
    compare x y | (Right z)
      = LT z
    compare x y | (Left z) with (decLT y x)
      compare x y | (Left z) | (Right w)
        = GT w
      compare x y | (Left z) | (Left w) with (isSymAnti z w)
        compare x x | (Left z) | (Left w) | Refl = EQ (refl x)

namespace MaxMin
  public export
  data Max : (lt,eq : (x,y : type) -> Decidable)
          -> (a,b,c : type) -> Type
    where
      RightMax  : forall lt . (prf : (lt x y).Positive) -> Max lt eq x y y
      EitherMax : forall lt . (prf : (eq x y).Positive) -> Max lt eq x y y
      LeftMax   : forall lt . (prf : (lt y x).Positive) -> Max lt eq x y x

  public export
  data Min : (lt,eq : (x,y : type) -> Decidable) -> (a,b,c : type) -> Type
    where
      RightMin  : forall lt . (prf : (lt x y).Positive) -> Min lt eq x y x
      EitherMin : forall lt . (prf : (eq x y).Positive) -> Min lt eq x y y
      LeftMin   : forall lt . (prf : (lt y x).Positive) -> Min lt eq x y y

  export
  max : DecORD type => (x,y : type) -> DPair type (Max LT EQ x y)
  max x y with (compare x y)
    max x y | (LT prf) = (y ** RightMax prf)
    max x y | (EQ prf) = (y ** EitherMax prf)
    max x y | (GT prf) = (x ** LeftMax prf)

  export
  min : DecORD type => (x,y : type) -> DPair type (Min LT EQ x y)
  min x y with (compare x y)
    min x y | (LT prf) = (x ** RightMin prf)
    min x y | (EQ prf) = (y ** EitherMin prf)
    min x y | (GT prf) = (y ** LeftMin prf)

-- [ EOF ]
