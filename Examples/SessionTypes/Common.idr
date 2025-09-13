module Examples.SessionTypes.Common

import Decidable.Positive
import Decidable.Positive.Dependent
import Decidable.Positive.Equality
import Decidable.Positive.Nat
import Decidable.Positive.String

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

-- [ EOF ]
