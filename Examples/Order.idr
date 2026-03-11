||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Order

import Data.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order

import Decidable.Positive.Nat

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
    isTrans = natTrans

    decLTE = natLTE

namespace SecLevel

  public export
  data SecLevel
     = SecretTop
     | Secret
     | Public

  public export
  data Same : (a,b : SecLevel) -> Type where
    PP : Same Public Public
    SS : Same Secret Secret
    TT : Same SecretTop SecretTop

  public export
  data SameNot : (a,b : SecLevel) -> Type where
    PS : SameNot Public Secret
    SP : SameNot Secret Public

    PT : SameNot Public SecretTop
    TP : SameNot SecretTop Public

    ST : SameNot Secret SecretTop
    TS : SameNot SecretTop Secret

  lemma : SameNot a b -> SameNot b a
  lemma PS = SP
  lemma SP = PS
  lemma PT = TP
  lemma TP = PT
  lemma ST = TS
  lemma TS = ST

  public export
  data LessThanEQ : (a,b : SecLevel) -> Type where
    LThanPP : LessThanEQ Public    Public
    LThanPS : LessThanEQ Public    Secret
    LThanPT : LessThanEQ Public    SecretTop
    LThanSS : LessThanEQ Secret    Secret
    LThanTS : LessThanEQ Secret    SecretTop
    LThanTT : LessThanEQ SecretTop SecretTop



  public export
  data GreaterThan : (a,b : SecLevel) -> Type where
    GThanTS : GreaterThan SecretTop Secret
    GThanTP : GreaterThan SecretTop Public
    GThanSP : GreaterThan Secret    Public

  secLevelCan : LessThanEQ a b -> GreaterThan a b -> Void
  secLevelCan LThanPP GThanTS impossible
  -- do not need other patterns

  secLevelEQ : Same a b -> SameNot a b -> Void
  secLevelEQ PP PS impossible
  -- do not need other patterns

  public export
  DecEQ SecLevel where
    EQUAL x y = D (Same x y) (SameNot x y) secLevelEQ

    toRefl PP = Refl
    toRefl SS = Refl
    toRefl TT = Refl

    toVoid PS Refl impossible
  -- do not need other patterns

    decEq SecretTop SecretTop = Right TT
    decEq SecretTop Secret = Left TS
    decEq SecretTop Public = Left TP
    decEq Secret SecretTop = Left ST
    decEq Secret Secret = Right SS
    decEq Secret Public = Left SP
    decEq Public SecretTop = Left PT
    decEq Public Secret = Left PS
    decEq Public Public = Right PP

    refl SecretTop = TT
    refl Secret = SS
    refl Public = PP

  public export
  DecORD SecLevel where
    LTE x y = D (LessThanEQ x y) (GreaterThan x y) secLevelCan

    isRefl LThanPP = Refl
    isRefl LThanSS = Refl
    isRefl LThanTT = Refl

    isSymAnti LThanPP LThanPP = Refl
    isSymAnti LThanSS LThanSS = Refl
    isSymAnti LThanTT LThanTT = Refl
    isSymAnti LThanPS LThanPP impossible
    -- do not need other patterns

    isTrans LThanPP LThanPP = LThanPP
    isTrans LThanPP LThanPS = LThanPS
    isTrans LThanPP LThanPT = LThanPT
    isTrans LThanPS LThanSS = LThanPS
    isTrans LThanPS LThanTS = LThanPT
    isTrans LThanPT LThanTT = LThanPT
    isTrans LThanSS LThanSS = LThanSS
    isTrans LThanSS LThanTS = LThanTS
    isTrans LThanTS LThanTT = LThanTS
    isTrans LThanTT LThanTT = LThanTT

    decLTE SecretTop SecretTop = Right LThanTT
    decLTE SecretTop Secret = Left GThanTS
    decLTE SecretTop Public = Left GThanTP
    decLTE Secret SecretTop = Right LThanTS
    decLTE Secret Secret = Right LThanSS
    decLTE Secret Public = Left GThanSP
    decLTE Public SecretTop = Right LThanPT
    decLTE Public Secret = Right LThanPS
    decLTE Public Public = Right LThanPP

-- [ EOF ]
