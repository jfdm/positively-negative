module Examples.SessionTypes.Binary.ChoiceNo

import public Decidable.Positive
import public Decidable.Positive.Dependent
import public Decidable.Positive.Equality
import public Decidable.Positive.String


%default total

data Action a = Send a (Action a)
              | Recv a (Action a)
              | Stop

--data Action : a -> Type where
--  Send : a -> Action a -> Action a
--  Recv : a -> Action a -> Action a
--  Stop : Action a


data Dual : (a    : Type)
         -> (pred : a -> a -> Decidable)
         -> (this, that : Action a)
         -> Type
  where
    DF : Dual a pred Stop Stop

    DS : {0 pred : a -> a -> Decidable}
      -> (  prf  : Positive (pred x y))
      -> (  ltr  : Dual a pred this that)
                -> Dual a pred (Send x this)
                               (Recv y that)

    DR : {0 pred : a -> a -> Decidable}
      -> (  prf  : Positive (pred x y))
      -> (  ltr  : Dual a pred this that)
                -> Dual a pred (Recv x this)
                               (Send y that)


data DualNot : (a : Type)
            -> (pred : a -> a -> Decidable)
            -> (this, that : Action a)
            -> Type
  where
    DFS : DualNot a neg Stop (Send x rest)
    DSF : DualNot a neg (Send x rest) Stop
    DFR : DualNot a neg Stop (Recv x rest)
    DRF : DualNot a neg (Recv x rest) Stop

    DSS : DualNot a pred (Send x this) (Send y that)
    DRR : DualNot a pred (Recv x this) (Recv y that)

    DSRL : (prf : Positive (pred x y))
        -> DualNot a pred (Send x this) (Recv y that)

    DRSL : (prf : Positive (pred x y))
               -> DualNot a pred (Recv x this) (Send y that)

    DSRLtr : (prf : Negative (pred x y))
          -> (ltr : DualNot a pred this that)
                 -> DualNot a pred (Send x this) (Recv y that)

    DRSLtr : (prf : Negative (pred x y))
          -> (ltr : DualNot a pred this that)
                 -> DualNot a pred (Recv x this) (Send y that)

0
cancelled : DecEQ a
         => Dual    a EQUAL    this that
         -> DualNot a EQUALNOT this that
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
  = (EQUAL _ _).Cancels prf x

cancelled (DS prf ltr) (DSRLtr x y)
  = cancelled ltr y

cancelled (DR prf ltr) (DRSL x)
  = (EQUAL _ _).Cancels prf x

cancelled (DR prf ltr) (DRSLtr x y)
  = cancelled ltr y

DUAL : {a : Type} -> DecEQ a => (x,y : Action a) -> Decidable
DUAL x y = D (Dual    _ EQUAL    x y)
             (DualNot _ EQUALNOT x y)
             cancelled

areDual : DecEQ a
       => (x,y : Action a)
              -> Dec (DUAL x y)
areDual (Send x z) (Recv y w) with (decEq x y)
  areDual (Send x z) (Recv y w) | (Left err)
    = Left (DSRL err)
  areDual (Send x z) (Recv y w) | (Right v) with (areDual z w)
    areDual (Send x z) (Recv y w) | (Right v) | (Left s)
      = Left (DSRLtr v s)
    areDual (Send x z) (Recv y w) | (Right v) | (Right s)
      = Right (DS v s)

areDual (Recv x z) (Send y w) with (decEq x y)
  areDual (Recv x z) (Send y w) | (Left v)
    = Left (DRSL v)
  areDual (Recv x z) (Send y w) | (Right v) with (areDual z w)
    areDual (Recv x z) (Send y w) | (Right v) | (Left s)
      = Left (DRSLtr v s)
    areDual (Recv x z) (Send y w) | (Right v) | (Right s)
      = Right (DR v s)

areDual (Send x z) (Send y w)
  = Left DSS
areDual (Send x z) Stop
  = Left DSF
areDual (Recv x z) (Recv y w)
  = Left DRR
areDual (Recv x z) Stop
  = Left DRF
areDual Stop (Send x y)
  = Left DFS
areDual Stop (Recv x y)
  = Left DFR
areDual Stop Stop
  = Right DF

namespace Discover

  0
  cancelled' : DecEQ a
           => (that : Action a)
           -> Dual    a EQUAL    this that
           -> DualNot a EQUALNOT this that
           -> Void
  cancelled' Stop DF DFS impossible
  cancelled' Stop DF DSF impossible
  cancelled' Stop DF DFR impossible
  cancelled' Stop DF DRF impossible
  cancelled' Stop DF DSS impossible
  cancelled' Stop DF DRR impossible
  cancelled' Stop DF (DSRL prf) impossible
  cancelled' Stop DF (DRSL prf) impossible
  cancelled' Stop DF (DSRLtr prf ltr) impossible
  cancelled' Stop DF (DRSLtr prf ltr) impossible

  cancelled' (Recv x that) (DS prf ltr) (DSRL y)
    = (EQUAL _ _).Cancels prf y

  cancelled' (Recv x that) (DS prf ltr) (DSRLtr y z)
    = cancelled' that ltr z

  cancelled' (Send x that) (DR prf ltr) (DRSL y)
    = (EQUAL _ _).Cancels prf y

  cancelled' (Send x that) (DR prf ltr) (DRSLtr y z)
    = cancelled' that ltr z

  public export
  DUAL : {a : Type} -> DecEQ a => (x : Action a) -> DDecidable
  DUAL x  = D (Action _)
               (Dual    _ EQUAL    x)
               (DualNot _ EQUALNOT x)
               cancelled'

  export
  computeDual : (x : Action String)
              -> POSITIVE (DUAL x)
  computeDual (Send str ltr) with (computeDual ltr)
    computeDual (Send str ltr) | (act ** rest)
      = (Recv str act ** DS (refl str) rest)

  computeDual (Recv str ltr) with (computeDual ltr)
    computeDual (Recv str ltr) | (act ** rest)
      = (Send str act ** DR (refl str) rest)

  computeDual Stop
    = (Stop ** DF)

-- [ EOF ]
