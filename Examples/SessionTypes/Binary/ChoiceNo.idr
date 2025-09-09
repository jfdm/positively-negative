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

areDual : DecEQ a => (x,y : Action a) -> Positive.Dec (DUAL x y)
areDual (Send x z) (Recv y w) with (Positive.decEq x y)
  areDual (Send x z) (Recv y w) | (Left err)
    = Left (DSRL err)
  areDual (Send x z) (Recv y w) | (Right v) with (areDual z w)
    areDual (Send x z) (Recv y w) | (Right v) | (Left s)
      = Left (DSRLtr v s)
    areDual (Send x z) (Recv y w) | (Right v) | (Right s)
      = Right (DS v s)

areDual (Recv x z) (Send y w) with (Positive.decEq x y)
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


0
cancelled' : DecEQ a
         => (that : Action a)
         -> Dual    a EQUAL Positive Negative this that
         -> DualNot a EQUAL Positive Negative this that
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
  = (EQUAL _ _).Cancelled prf y

cancelled' (Recv x that) (DS prf ltr) (DSRLtr y z)
  = cancelled' that ltr z

cancelled' (Send x that) (DR prf ltr) (DRSL y)
  = (EQUAL _ _).Cancelled prf y

cancelled' (Send x that) (DR prf ltr) (DRSLtr y z)
  = cancelled' that ltr z

DUAL' : {a : Type} -> DecEQ a => (x : Action a) -> DDecidable
DUAL' x  = D (Action _)
             (Dual    _ EQUAL Positive Negative x)
             (DualNot _ EQUAL Positive Negative x)
             cancelled'

computeDual' : (x : Action String) -> DPair (Action String) (Positive.Dec . DUAL x)
computeDual' (Send x y) with (computeDual' y)
  computeDual' (Send x y) | (fst ** (Left z)) = (Recv x fst ** Left $ DSRLtr (refl x) z)
  computeDual' (Send x y) | (fst ** (Right z)) = (Recv x fst ** Right $ DS (refl x) z)
computeDual' (Recv x y) with (computeDual' y)
  computeDual' (Recv x y) | (fst ** (Left z)) = (Send x fst ** Left $ DRSLtr (refl x) z)
  computeDual' (Recv x y) | (fst ** (Right z)) = (Send x fst ** Right $ DR (refl x) z)
computeDual' Stop = (Stop ** Right DF)

computeDual : (x : Action String) -> Positive.DDec (DUAL' x)
computeDual (Send x y) with (computeDual y)
  computeDual (Send x y) | (Left (fst ** snd)) = Left (Recv x fst ** DSRLtr (refl x) snd)
  computeDual (Send x y) | (Right (fst ** snd)) = Right (Recv x fst ** DS (refl x) snd)
computeDual (Recv x y) with (computeDual y)
  computeDual (Recv x y) | (Left (fst ** snd)) = Left (Send x fst ** DRSLtr (refl x) snd)
  computeDual (Recv x y) | (Right (fst ** snd)) = Right (Send x fst ** DR (refl x) snd)

computeDual Stop = Right (Stop ** DF)
