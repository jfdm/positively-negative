||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Order.SQA

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order

public export
data Level = Nat5 | H | AH

public export
data Same : (x,y : Level) -> Type
  where
    SameNN : Same Nat5 Nat5
    SameHH : Same H    H
    SameAA : Same AH   AH

public export
data SameNot : (x,y : Level) -> Type
  where
    SameNotNH : SameNot Nat5 H
    SameNotNA : SameNot Nat5 AH
    SameNotHA : SameNot H    AH

    SameNotHN : SameNot H    Nat5
    SameNotAN : SameNot AH   Nat5
    SameNotAH : SameNot AH   H

public export
negSym : SQA.SameNot a b -> SQA.SameNot b a
negSym SameNotNH = SameNotHN
negSym SameNotNA = SameNotAN
negSym SameNotHA = SameNotAH
negSym SameNotHN = SameNotNH
negSym SameNotAN = SameNotNA
negSym SameNotAH = SameNotHA

sqaEqCan : SQA.Same a b -> SQA.SameNot a b -> Void
sqaEqCan SameNN SameNotNH impossible
-- do not need other patterns

public export
data LTE : (a, b : Level) -> Type
  where
    LThanEqNN : LTE Nat5 Nat5
    LThanEqNH : LTE Nat5 H
    LThanEqNA : LTE Nat5 AH
    LThanEqHH : LTE H    H
    LThanEqHA : LTE H    AH
    LThanEqAA : LTE AH   AH

public export
data GT : (a, b : Level) -> Type
  where
    GThanAH : GT AH H
    GThanAN : GT AH Nat5
    GThanHN : GT H  Nat5


sqaCancelled : {x,y : Level}
            -> LTE x y
            -> GT  x y
            -> Void
sqaCancelled LThanEqNN GThanAH impossible
-- do not need other patterns

public export
DecEQ SQA.Level where
  EQUAL x y = D (Same x y) (SameNot x y) sqaEqCan

  toRefl SameNN = Refl
  toRefl SameHH = Refl
  toRefl SameAA = Refl

  refl Nat5 = SameNN
  refl H = SameHH
  refl AH = SameAA

  toVoid SameNotNH Refl impossible
  -- do not need other patterns

  decEq Nat5 Nat5 = Right SameNN
  decEq Nat5 H = Left SameNotNH
  decEq Nat5 AH = Left SameNotNA
  decEq H Nat5 = Left SameNotHN
  decEq H H = Right SameHH
  decEq H AH = Left SameNotHA
  decEq AH Nat5 = Left SameNotAN
  decEq AH H = Left SameNotAH
  decEq AH AH = Right SameAA

public export
DecORD SQA.Level where
  LTE x y = D (LTE x y) (GT x y) sqaCancelled

  isRefl LThanEqNN = Refl
  isRefl LThanEqHH = Refl
  isRefl LThanEqAA = Refl

  isSymAnti LThanEqNN LThanEqNN = Refl
  isSymAnti LThanEqHH LThanEqHH = Refl
  isSymAnti LThanEqAA LThanEqAA = Refl
  isSymAnti LThanEqHA LThanEqNN impossible
  -- do not need to provide the other cases

  isTrans LThanEqNN LThanEqNN = LThanEqNN
  isTrans LThanEqNN LThanEqNH = LThanEqNH
  isTrans LThanEqNN LThanEqNA = LThanEqNA
  isTrans LThanEqNH LThanEqHH = LThanEqNH
  isTrans LThanEqNH LThanEqHA = LThanEqNA
  isTrans LThanEqNA LThanEqAA = LThanEqNA
  isTrans LThanEqHH LThanEqHH = LThanEqHH
  isTrans LThanEqHH LThanEqHA = LThanEqHA
  isTrans LThanEqHA LThanEqAA = LThanEqHA
  isTrans LThanEqAA LThanEqAA = LThanEqAA

  decLTE Nat5 Nat5 = Right LThanEqNN
  decLTE Nat5 H = Right LThanEqNH
  decLTE Nat5 AH = Right LThanEqNA
  decLTE H Nat5 = Left GThanHN
  decLTE H H = Right LThanEqHH
  decLTE H AH = Right LThanEqHA
  decLTE AH Nat5 = Left GThanAN
  decLTE AH H = Left GThanAH
  decLTE AH AH = Right LThanEqAA



public export
OLevel : Type
OLevel = Pair Nat SQA.Level
{-
  public export
  data Same : (x,y : Level) -> Type
    where
      SameNN : Same Nat5 Nat5
      SameHH : Same H    H
      SameAA : Same AH   AH

  public export
  data SameNot : (x,y : Level) -> Type
    where
      SameNotNH : SameNot Nat5 H
      SameNotNA : SameNot Nat5 AH
      SameNotHA : SameNot H    AH

      SameNotHN : SameNot H    Nat5
      SameNotAN : SameNot AH   Nat5
      SameNotAH : SameNot AH   H

  public export
  negSym : SQA.SameNot a b -> SQA.SameNot b a
  negSym SameNotNH = SameNotHN
  negSym SameNotNA = SameNotAN
  negSym SameNotHA = SameNotAH
  negSym SameNotHN = SameNotNH
  negSym SameNotAN = SameNotNA
  negSym SameNotAH = SameNotHA

  sqaEqCan : SQA.Same a b -> SQA.SameNot a b -> Void
  sqaEqCan SameNN SameNotNH impossible
  -- do not need other patterns

  public export
  data LTE : (a, b : Level) -> Type
    where
      LThanEqNN : LTE Nat5 Nat5
      LThanEqNH : LTE Nat5 H
      LThanEqNA : LTE Nat5 AH
      LThanEqHH : LTE H    H
      LThanEqHA : LTE H    AH
      LThanEqAA : LTE AH   AH

  public export
  data GT : (a, b : Level) -> Type
    where
      GThanAH : GT AH H
      GThanAN : GT AH Nat5
      GThanHN : GT H  Nat5


  sqaCancelled : {x,y : Level}
              -> LTE x y
              -> GT  x y
              -> Void
  sqaCancelled LThanEqNN GThanAH impossible
  -- do not need other patterns

  public export
  DecEQ SQA.Level where
    EQUAL x y = D (Same x y) (SameNot x y) sqaEqCan

    toRefl SameNN = Refl
    toRefl SameHH = Refl
    toRefl SameAA = Refl

    refl Nat5 = SameNN
    refl H = SameHH
    refl AH = SameAA

    toVoid SameNotNH Refl impossible
    -- do not need other patterns

    decEq Nat5 Nat5 = Right SameNN
    decEq Nat5 H = Left SameNotNH
    decEq Nat5 AH = Left SameNotNA
    decEq H Nat5 = Left SameNotHN
    decEq H H = Right SameHH
    decEq H AH = Left SameNotHA
    decEq AH Nat5 = Left SameNotAN
    decEq AH H = Left SameNotAH
    decEq AH AH = Right SameAA

  public export
  DecORD SQA.Level where
    LTE x y = D (LTE x y) (GT x y) sqaCancelled

    isRefl LThanEqNN = Refl
    isRefl LThanEqHH = Refl
    isRefl LThanEqAA = Refl

    isSymAnti LThanEqNN LThanEqNN = Refl
    isSymAnti LThanEqHH LThanEqHH = Refl
    isSymAnti LThanEqAA LThanEqAA = Refl
    isSymAnti LThanEqHA LThanEqNN impossible
    -- do not need to provide the other cases

    isTrans LThanEqNN LThanEqNN = LThanEqNN
    isTrans LThanEqNN LThanEqNH = LThanEqNH
    isTrans LThanEqNN LThanEqNA = LThanEqNA
    isTrans LThanEqNH LThanEqHH = LThanEqNH
    isTrans LThanEqNH LThanEqHA = LThanEqNA
    isTrans LThanEqNA LThanEqAA = LThanEqNA
    isTrans LThanEqHH LThanEqHH = LThanEqHH
    isTrans LThanEqHH LThanEqHA = LThanEqHA
    isTrans LThanEqHA LThanEqAA = LThanEqHA
    isTrans LThanEqAA LThanEqAA = LThanEqAA

    decLTE Nat5 Nat5 = Right LThanEqNN
    decLTE Nat5 H = Right LThanEqNH
    decLTE Nat5 AH = Right LThanEqNA
    decLTE H Nat5 = Left GThanHN
    decLTE H H = Right LThanEqHH
    decLTE H AH = Right LThanEqHA
    decLTE AH Nat5 = Left GThanAN
    decLTE AH H = Left GThanAH
    decLTE AH AH = Right LThanEqAA
-}
