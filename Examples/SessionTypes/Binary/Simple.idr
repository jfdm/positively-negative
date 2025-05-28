module Examples.SessionTypes.Binary.Simple

import public Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.String


%default total

namespace Simple
  data Action : a -> Type where
    Send : a -> Action a -> Action a
    Recv : a -> Action a -> Action a
    Stop : Action a


  data Dual : (a    : Type)
           -> (pred : a -> a -> Decidable)
           -> (pos  : Decidable -> Type)
           -> (neg  : Decidable -> Type)
           -> (this, that : Action a)
           -> Type
    where
      DF : Dual a pred pos neg Stop Stop

      DS : {0 pred : a -> a -> Decidable}
        -> (  prf  : pos (pred x y))
        -> (  ltr  : Dual a pred pos neg this that)
                  -> Dual a pred pos neg (Send x this)
                                       (Recv y that)

      DR : {0 pred : a -> a -> Decidable}
        -> (  prf  : pos (pred x y))
        -> (  ltr  : Dual a pred pos neg this that)
                  -> Dual a pred pos neg (Recv x this)
                                         (Send y that)


  data DualNot : (a : Type)
              -> (pred : a -> a -> Decidable)
              -> (pos  : Decidable -> Type)
              -> (neg  : Decidable -> Type)
              -> (this, that : Action a)
              -> Type
    where
      DFS : DualNot a pred pos neg Stop (Send x rest)
      DSF : DualNot a pred pos neg (Send x rest) Stop
      DFR : DualNot a pred pos neg Stop (Recv x rest)
      DRF : DualNot a pred pos neg (Recv x rest) Stop

      DSS : DualNot a pred pos neg (Send x this) (Send y that)
      DRR : DualNot a pred pos neg (Recv x this) (Recv y that)

      DSRL : (prf : neg (pred x y))
          -> DualNot a pred pos neg (Send x this) (Recv y that)

      DRSL : (prf : neg (pred x y))
                 -> DualNot a pred pos neg (Recv x this) (Send y that)

      DSRLtr : (prf : pos (pred x y))
            -> (ltr : DualNot a pred pos neg this that)
                   -> DualNot a pred pos neg (Send x this) (Recv y that)

      DRSLtr : (prf : pos (pred x y))
            -> (ltr : DualNot a pred pos neg this that)
                   -> DualNot a pred pos neg (Recv x this) (Send y that)

  0
  cancelled : DecEQ a
           => Dual    a EQUAL Positive Negative this that
           -> DualNot a EQUAL Positive Negative this that
           -> Void
  cancelled DF DFS impossible
  cancelled DF DSF impossible
  cancelled DF DFR impossible
  cancelled DF DRF impossible
  cancelled DF DSS impossible
  cancelled DF DRR impossible
  cancelled DF (DSRL prf) impossible
  cancelled DF (DRSL prf) impossible
  cancelled DF (DSRLtr prf ltr) impossible
  cancelled DF (DRSLtr prf ltr) impossible

  cancelled (DS prf ltr) (DSRL x)
    = (EQUAL _ _).Cancelled prf x

  cancelled (DS prf ltr) (DSRLtr x y)
    = cancelled ltr y

  cancelled (DR prf ltr) (DRSL x)
    = (EQUAL _ _).Cancelled prf x

  cancelled (DR prf ltr) (DRSLtr x y)
    = cancelled ltr y

  DUAL : {a : Type} -> DecEQ a => (x,y : Action a) -> Decidable
  DUAL x y = D (Dual    _ EQUAL Positive Negative x y)
               (DualNot _ EQUAL Positive Negative x y)
               cancelled

  dual : DecEQ a => (x,y : Action a) -> Positive.Dec (DUAL x y)
  dual (Send x z) (Recv y w) with (Positive.decEq x y)
    dual (Send x z) (Recv y w) | (Left err)
      = Left (DSRL err)
    dual (Send x z) (Recv y w) | (Right v) with (dual z w)
      dual (Send x z) (Recv y w) | (Right v) | (Left s)
        = Left (DSRLtr v s)
      dual (Send x z) (Recv y w) | (Right v) | (Right s)
        = Right (DS v s)

  dual (Recv x z) (Send y w) with (Positive.decEq x y)
    dual (Recv x z) (Send y w) | (Left v)
      = Left (DRSL v)
    dual (Recv x z) (Send y w) | (Right v) with (dual z w)
      dual (Recv x z) (Send y w) | (Right v) | (Left s)
        = Left (DRSLtr v s)
      dual (Recv x z) (Send y w) | (Right v) | (Right s)
        = Right (DR v s)

  dual (Send x z) (Send y w)
    = Left DSS
  dual (Send x z) Stop
    = Left DSF
  dual (Recv x z) (Recv y w)
    = Left DRR
  dual (Recv x z) Stop
    = Left DRF
  dual Stop (Send x y)
    = Left DFS
  dual Stop (Recv x y)
    = Left DFR
  dual Stop Stop
    = Right DF
