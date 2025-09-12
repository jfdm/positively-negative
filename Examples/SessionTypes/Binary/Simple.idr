module Examples.SessionTypes.Binary.Simple

import public Decidable.Positive
import public Decidable.Positive.Dependent
import public Decidable.Positive.Equality
import public Decidable.Positive.Nat
import public Decidable.Positive.String


%default total

namespace CType
  public export
  data CType = SEND | RECV

  public export
  data EQ : CType -> CType -> Type where
    SS : EQ SEND SEND
    RR : EQ RECV RECV

  public export
  data EQN : CType -> CType -> Type where
    SR : EQN SEND RECV
    RS : EQN RECV SEND

  public export
  DecEQ CType where
    EQUAL x y
      = D (EQ x y) (EQN x y) prf
      where
      prf : forall x, y . EQ x y -> EQN x y -> Void
      prf SS SR impossible
      prf SS RS impossible
      prf RR SR impossible
      prf RR RS impossible

    toRefl SS = Refl
    toRefl RR = Refl

    toVoid SR Refl impossible
    toVoid RS Refl impossible

    decEq SEND SEND = Right SS
    decEq SEND RECV = Left SR

    decEq RECV SEND = Left RS
    decEq RECV RECV = Right RR

    refl SEND = SS
    refl RECV = RR

namespace OType
  public export
  data OType = OFFER | CHOICE

  public export
  data EQ : OType -> OType -> Type where
    OO : EQ OFFER OFFER
    CC : EQ CHOICE CHOICE

  public export
  data EQN : OType -> OType -> Type where
    OC : EQN OFFER CHOICE
    CO : EQN CHOICE OFFER

  public export
  DecEQ OType where
    EQUAL x y
      = D (EQ x y) (EQN x y) prf
      where
      prf : forall x, y . OType.EQ x y -> OType.EQN x y -> Void
      prf OO OC impossible
      prf OO CO impossible
      prf CC OC impossible
      prf CC CO impossible

    toRefl OO = Refl
    toRefl CC = Refl

    toVoid OC Refl impossible
    toVoid CO Refl impossible

    decEq OFFER OFFER = Right OO
    decEq OFFER CHOICE = Left OC

    decEq CHOICE OFFER = Left CO
    decEq CHOICE CHOICE = Right CC

    refl OFFER = OO
    refl CHOICE = CC

data Action a = A CType a (Action a)
              | O OType (Action a) (Action a)
              | Stop

data Dual : (a    : Type)
         -> (pred : a -> a -> Decidable)
         -> (this, that : Action a)
         -> Type
  where
    DF : Dual a p Stop Stop

    DA : (eq  : Positive (EQUALNOT s r))
      -> (prf : Positive (p x y))
      -> (ltr : Dual a p this that)
             -> Dual a p (A s x this)
                         (A r y that)

    DC : (eq  : Positive (EQUALNOT x y))
      -> (l : Dual a p thisL thatL)
      -> (r : Dual a p thisR thatR)
             -> Dual a p (O x thisL thisR)
                         (O y thatL thatR)

data DualNot : (a : Type)
            -> (pred : a -> a -> Decidable)
            -> (this, that : Action a)
            -> Type
  where
    DFA : DualNot a p Stop (A c x rest)
    DFO : DualNot a p Stop (O c l r)

    DAF : DualNot a p (A c x rest) Stop
    DOF : DualNot a p (O c l r)    Stop

    DOA : DualNot a p (O c l r)   (A t x ltr)
    DAO : DualNot a p (A t x ltr) (O c l r)

    DAT : (prf : Positive (EQUAL x y))
              -> DualNot a p (A x i this) (A y j that)

    DAL : (prfL : Positive (EQUALNOT i j))
       -> (prfT : Positive (p x y))
               -> DualNot a p (A i x this) (A j y that)

    DAR : (prfL : Positive (EQUALNOT i j))
       -> (prfT : Negative (p x y))
        -> (ltr : DualNot a p this that)
                -> DualNot a p (A i x this) (A j y that)

    DOT : (prf : Positive (EQUAL x y))
              -> DualNot a p (O x l r) (O y i j)

    DOL : (prfK : Positive (EQUALNOT x y))
       -> (prfL : DualNot a p l i)
              -> DualNot a p (O x l r) (O y i j)

    DOR : (prfK : Positive (EQUALNOT x y))
--       -> (prfL : Dual a p l i)
       -> (prfR : DualNot a p r j)
              -> DualNot a p (O x l r) (O y i j)

namespace Check

  0
  prf : DecEQ a
     => (Dual    a EQUAL    x y)
     -> (DualNot a EQUALNOT x y)
     -> Void
  prf DF DFA impossible
  prf DF DFO impossible
  prf DF DAF impossible
  prf DF DOF impossible
  prf DF DOA impossible
  prf DF DAO impossible
  prf DF (DAT pr) impossible
  prf DF (DAL prfL prfT) impossible
  prf DF (DAR prfL prfT ltr) impossible
  prf DF (DOT pf) impossible
  prf DF (DOL prfK prfL) impossible
  prf DF (DOR prfK prfR) impossible

  prf {x=A x i l} {y=A y j r} (DA eq _ _) (DAT pr)
    = (EQUALNOT x y).Cancels eq pr

  prf {x=A x i l} {y=A y j r} (DA _ p _) (DAL _ prfT)
    = (EQUAL i j).Cancels p prfT

  prf {x=A x i l} {y=A y j r} (DA _ _ ltrY) (DAR _ _ ltrN)
    = prf ltrY ltrN

  prf {x=O x i a} {y=O y j b} (DC eq _ _) (DOT pf)
    = (EQUALNOT x y).Cancels eq pf

  prf (DC _ l _) (DOL _ prfL)
    = prf l prfL

  prf (DC _ _ r) (DOR _ prfR)
    = prf r prfR

  public export
  DUAL : {a : Type}
      -> DecEQ a
      => (x,y : Action a)
             -> Decidable
  DUAL x y
    = D (Dual    _ EQUAL    x y)
        (DualNot _ EQUALNOT x y)
        prf

  export
  dual : DecEQ a
      => (x,y : Action a)
             -> Dec (DUAL x y)
  dual (A a i x) (A b j y)
    = do pK <- decEqNot a b `otherwise` DAT
         pT <- decEq i j `otherwise` (DAL pK)
         pR <- dual x y `otherwise` (DAR pK pT)
         pure (DA pK pT pR)

  dual (A _ _ _) (O _ _ _)
    = Left DAO
  dual (A _ _ _) Stop
    = Left DAF

  dual (O _ _ _) (A _ _ _)
    = Left DOA

  dual (O a i x) (O b j y)
    = do pK <- decEqNot a b `otherwise` DOT
         pT <- dual i j `otherwise` (DOL pK)
         pR <- dual x y `otherwise` (DOR pK)
         pure (DC pK pT pR)

  dual (O _ _ _) Stop
    = Left DOF

  dual Stop (A _ _ _)
    = Left DFA
  dual Stop (O _ _ _)
    = Left DFO

  dual Stop Stop = Right DF

test1 : Action Nat
test1
  = A SEND 1
  $ A RECV 2
  $ O OFFER Stop Stop

test2 : Action Nat
test2
  = A RECV 1
  $ A SEND 2
  $ O CHOICE Stop (A SEND 3 Stop)
