module Examples.SessionTypes.Binary.ChoiceNo

import public Decidable.Positive
import public Decidable.Positive.Dependent
import public Decidable.Positive.Equality
import public Decidable.Positive.String

import public Examples.SessionTypes.Common

%default total

data Action a = A CType a (Action a)
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

    DA : {0 pred : a -> a -> Decidable}
      -> (  prf  : Positive (EQUALNOT i j))
      -> (  prf  : Positive (pred x y))
      -> (  ltr  : Dual a pred this that)
                -> Dual a pred (A i x this)
                               (A j y that)

data DualNot : (a : Type)
            -> (pred : a -> a -> Decidable)
            -> (this, that : Action a)
            -> Type
  where
    DFA : DualNot a p Stop (A c x rest)

    DAF : DualNot a p (A c x rest) Stop

    DAT : (prf : Positive (EQUAL x y))
              -> DualNot a p (A x i this) (A y j that)

    DAL : (prfL : Positive (EQUALNOT i j))
       -> (prfT : Positive (p x y))
               -> DualNot a p (A i x this) (A j y that)

    DAR : (prfL : Positive (EQUALNOT i j))
       -> (prfT : Negative (p x y))
        -> (ltr : DualNot a p this that)
                -> DualNot a p (A i x this) (A j y that)


0
cancelled : DecEQ a
         => Dual    a         p  this that
         -> DualNot a (\x,y => Swap $ p x y) this that
         -> Void
cancelled DF DFA impossible
cancelled DF DAF impossible
cancelled DF (DAT prf) impossible
cancelled DF (DAL prfL prfT) impossible
cancelled DF (DAR prfL prfT ltr) impossible

cancelled {this=A i x l} {that=A j y m} (DA px _ _) (DAT py)
  = (EQUALNOT i j).Cancels px py
cancelled {this=A i x l} {that=A j y m} (DA _ px _) (DAL _ py)
  = (p x y).Cancels px py

cancelled (DA _ _ x) (DAR _ _ y)
  = cancelled x y



DUAL : {a : Type} -> DecEQ a => (x,y : Action a) -> Decidable
DUAL x y = D (Dual    _ EQUAL    x y)
             (DualNot _ EQUALNOT x y)
             cancelled


areDual : DecEQ a
       => (x,y : Action a)
              -> Dec (DUAL x y)
areDual (A i x g) (A j y h)
    = do pK <- decEqNot i j `otherwise` DAT
         pT <- decEq x y `otherwise` (DAL pK)
         pR <- areDual g h `otherwise` (DAR pK pT)
         pure (DA pK pT pR)

areDual (A _ _ _) Stop
  = Left DAF

areDual Stop (A _ _ _)
  = Left DFA
areDual Stop Stop
  = Right DF


namespace Discover

  0
  cancelled' : DecEQ a
           => (that : Action a)
           -> Dual    a p    this that
           -> DualNot a (\x,y => Swap $ p x y) this that
           -> Void
  cancelled' Stop DF DFA impossible
  cancelled' Stop DF DAF impossible
  cancelled' Stop DF (DAT prf) impossible
  cancelled' Stop DF (DAL prfL prfT) impossible
  cancelled' Stop DF (DAR prfL prfT ltr) impossible

  cancelled' (A ty _ _) (DA prf _ _) (DAT y)
    = (EQUAL _ ty).Cancels y prf

  cancelled' (A _ x _) (DA _ y _) (DAL _ z)
    = (p _ _).Cancels y z

  cancelled' (A _ _ x) (DA _ _ py) (DAR _ _ pn)
    = cancelled' x py pn


  public export
  DUAL : {a : Type} -> DecEQ a => (x : Action a) -> DDecidable
  DUAL x  = D (Action _)
               (Dual    _ EQUAL    x)
               (DualNot _ EQUALNOT x)
               cancelled'

  export
  computeDual : (x : Action String)
              -> POSITIVE (DUAL x)
  computeDual (A SEND str ltr) with (computeDual ltr)
    computeDual (A SEND str ltr) | (act ** rest)
      = (A RECV str act ** DA SR (refl str) rest)

  computeDual (A RECV str ltr) with (computeDual ltr)
    computeDual (A RECV str ltr) | (act ** rest)
      = (A SEND str act ** DA RS (refl str) rest)

  computeDual Stop
    = (Stop ** DF)

-- [ EOF ]
