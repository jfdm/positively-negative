||| Decidable ordering based on partially ordered sets.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Order

import Decidable.Positive

import Data.Nat

namespace Postitive
  ||| A Positive Decision about Ordering
  public export
  interface DecORD type where

      LTE : (x,y : type) -> Decidable

      isRefl : {a   : type}
            -> (prf : (LTE a a).Positive)
                   -> (a = a)

      isSymAnti : {a,b : type}
               -> (prfLTE : (LTE a b).Positive)
               -> (prfGTE : (LTE b a).Positive)
                         -> (a = b)

      isSymAntiDiag : {a,b : type}
                   -> (prfLTE : (LTE a b).Positive)
                   -> (prfGTE : (LTE b a).Negative)
                             -> (a = b)

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
  data LessThan : (lte : (x,y : type) -> Decidable)
               -> (x,y : type)
                      -> Type
    where
      IsLT : forall lte
           . (prfLTE    : (lte x y).Positive)
          -> (prfGteNot : (lte y x).Negative)
                        -> LessThan lte x y

  public export
  data GreaterThanEQ : (lte : (x,y : type) -> Decidable)
                    -> (x,y : type)
                           -> Type
    where
      IsGTE : forall lte
            . Either ((lte y x).Positive) ((lte x y).Negative)
           -> GreaterThanEQ lte x y

  0
  prfLtGTE : DecORD type
          => {x,y : type}
          -> LessThan  LTE x y
          -> GreaterThanEQ LTE x y
          -> Void
  prfLtGTE {x = x} {y = y} prfLT prfGTE with (prfLT)
    prfLtGTE {x = x} {y = y} prfLT prfGTE | (IsLT prfLTE prfGteNot) with (prfGTE)
      prfLtGTE {x = x} {y = y} prfLT prfGTE | (IsLT prfLTE prfGteNot) | (IsGTE (Left prfGT))
        = (GT y x).Cancels prfGteNot prfGT
      prfLtGTE {x = x} {y = y} prfLT prfGTE | (IsLT prfLTE prfGteNot) | (IsGTE (Right prfGT))
        = (LTE x y).Cancels prfLTE prfGT

  public export
  LT : DecORD type => (x,y : type) -> Decidable
  LT x y = D (LessThan LTE x y) (GreaterThanEQ LTE x y) prfLtGTE

  export
  decLT : DecORD type => (x,y : type) -> Positive.Dec (LT x y)
  decLT x y with (decLTE x y)
    decLT x y | (Left prfGT) = Left (IsGTE (Right prfGT))

    decLT x y | (Right prfLTE) with (decGT y x)
      decLT x y | (Right prfLTE) | (Left prfLT)
        = Left (IsGTE (Left prfLT))
      decLT x y | (Right prfLTE) | (Right prfGT)
        = Right (IsLT prfLTE prfGT)


  public export
  GTE : DecORD type => (x,y : type) -> Decidable
  GTE x y = Swap (LT x y)

  public export
  decGTE : DecORD type
        => (x,y : type)
               -> Positive.Dec (GTE x y)
  decGTE x y = mirror (decLT x y)

namespace Compare
  public export
  data Compare : (lt : (x,y : type) -> Decidable)
              -> (a,b : type)
                     -> Type
    where
      BiasLeft  : forall lt . (prf : (lt a b).Positive) -> Compare lt a b
      BiasSame  : forall lt . (prf : a = b) -> Compare lt a b
      BiasRight : forall lt . (prf : (lt b a).Positive) -> Compare lt a b

  export
  compare : DecORD type => (x,y : type) -> Compare LT x y
  compare x y with (decLT x y)
    compare x y | (Right z)
      = BiasLeft z
    compare x y | (Left z) with (decLT y x)
      compare x y | (Left z) | (Right w)
        = BiasRight w
      compare x y | (Left z) | (Left w) = ?kk
{-
||| Propositions to capture how elements are related by their order.
namespace Ordering
||| Propositions to chose the larger or smaller element.
namespace MaxMin
  public export
  data Max : (lt : (x,y : type) -> Type) -> (a,b,c : type) -> Type
    where
      RightMax : {lt : (x,y : type) -> Type}
            -> (prf : lt x y)
                   -> Max lt x y y

      EitherMax : (prf : Equal x y)
                     -> Max lt x y y

      LeftMax : {lt : (x,y : type) -> Type}
             -> (prf : lt y x)
                    -> Max lt x y x

  public export
  data Min : (lt : (x,y : type) -> Type) -> (a,b,c : type) -> Type
    where
      RightMin : {lt  : (x,y : type) -> Type}
              -> (prf : lt x y)
                      -> Min lt x y x

      EitherMin : (prf : Equal x y)
                     -> Min lt x y y

      LeftMin : {lt : (x,y : type) -> Type}
             -> (prf : lt y x)
                    -> Min lt x y y
-}

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


  natSymAntiD : {x,y : Nat}
             -> Nat.LTE x y
             -> Nat.GT y x
             -> x = y
  natSymAntiD z w = ?natSymAntiD_rhs


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
    isSymAntiDiag = natSymAntiD
    isTrans = natTrans

    decLTE = natLTE


-- [ EOF ]
