||| STLC Types
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Elab.STLC.Types

import Data.Either
import Data.Singleton

import public Decidable.Positive
import public Decidable.Positive.Equality

public export
data Ty = NAT | FUNC Ty Ty

export
Show Ty where
  show NAT = "Nat"
  show (FUNC a b) = "(\{show a} -> \{show b})"

public export
data AreEqual : Ty -> Ty -> Type where
  NN : AreEqual NAT NAT
  FF : AreEqual       x          a
    -> AreEqual         y          b
    -> AreEqual (FUNC x y) (FUNC a b)

symEQ : Types.AreEqual a b
     -> Types.AreEqual b a
symEQ NN
  = NN
symEQ (FF x y)
  = FF (symEQ x) (symEQ y)

public export
data AreEqualNot : Ty -> Ty -> Type where
  NF : AreEqualNot NAT (FUNC x y)
  FN : AreEqualNot (FUNC x y) NAT
  FA : AreEqualNot x a -> AreEqualNot (FUNC x y) (FUNC a b)
  FR : AreEqualNot y b -> AreEqualNot (FUNC x y) (FUNC a b)

public export
dup : (ty : Ty) -> AreEqual ty ty
dup NAT = NN
dup (FUNC x y) = FF (dup x) (dup y)

helper : (e,f : Ty) -> String
helper e f
  = "Expected:\n\n\{show e}\n\nbut given:\n\n\{show f}"

export
show : {x,y : Ty} -> (Types.AreEqualNot x y) -> String
show {x = NAT} {y = (FUNC x y)} NF
  = helper NAT (FUNC x y)

show {y = NAT} {x = (FUNC x y)} FN
  = helper (FUNC x y) NAT

show {x = (FUNC x y)} {y = (FUNC a b)} (FA z)
  = "\{helper (FUNC x y) (FUNC a b)}\n\nSpecifically, the argument type differs:\n\n\{Types.show z}"

show {x = (FUNC x y)} {y = (FUNC a b)} (FR z)
  = "\{helper (FUNC x y) (FUNC a b)}\n\nSpecifically, the return type differs:\n\n\{Types.show z}"

public export
symEQN : Types.AreEqualNot a b -> Types.AreEqualNot b a
symEQN NF = FN
symEQN FN = NF
symEQN (FA x) = FA (symEQN x)
symEQN (FR x) = FR (symEQN x)

public export
isVoid : AreEqual x y -> Types.AreEqualNot x y -> Void
isVoid NN NF impossible
isVoid NN (FA z) impossible
isVoid NN (FR z) impossible

isVoid (FF z v) (FA w) = isVoid z w
isVoid (FF z v) (FR w) = isVoid v w

public export
isEq : Types.AreEqual x y -> Equal x y
isEq NN
  = Refl
isEq (FF z w) with (isEq z)
  isEq (FF z w) | Refl with (isEq w)
    isEq (FF z w) | Refl | Refl = Refl

export
isNeg : Types.AreEqualNot x y
     -> Equal x y
     -> Void
isNeg (FA z) Refl with (isNeg z)
  isNeg (FA z) Refl | boom
    = boom Refl
isNeg (FR z) Refl with (isNeg z)
  isNeg (FR z) Refl | boom
    = boom Refl

public export
DecEQ Ty where

  EQUAL x y = D (AreEqual x y) (AreEqualNot x y) isVoid

  toRefl = isEq

  toVoid = isNeg

  decEq NAT NAT
    = Right NN

  decEq NAT (FUNC x y)
    = Left NF

  decEq (FUNC x z) NAT
    = Left (symEQN NF)

  decEq (FUNC x z) (FUNC a b) with (decEq x a)
    decEq (FUNC x z) (FUNC a b) | (Left err)
      = Left (FA err)

    decEq (FUNC x z) (FUNC a b) | (Right vdom) with (decEq z b)
      decEq (FUNC x z) (FUNC a b) | (Right vdom) | (Left err)
        = Left (FR err)

      decEq (FUNC x z) (FUNC a b) | (Right vdom) | (Right vdomco)
        = Right (FF vdom vdomco)

  refl = dup

public export
data IsFunc : Ty -> Type where
  YIF : IsFunc (FUNC x y)

public export
data IsNat : Ty -> Type where
  YIN : IsNat NAT

cancelled : IsFunc ty -> IsNat ty -> Void
cancelled YIF YIN impossible

public export
ISFUNC : Ty -> Decidable
ISFUNC ty = D (IsFunc ty) (IsNat ty) cancelled

public export
ISNAT : Ty -> Decidable
ISNAT = Swap . ISFUNC

export
isFunc : (ty : Ty) -> Dec (ISFUNC ty)
isFunc NAT = Left YIN
isFunc (FUNC x y) = Right YIF

export
isNat : (ty : Ty) -> Dec (ISNAT ty)
isNat ty = mirror (isFunc ty)


public export
sameDomain : AreEqual (FUNC a b) (FUNC x y) -> AreEqual a x
sameDomain (FF z w) = z

public export
sameDomainCo : AreEqual (FUNC a b) (FUNC x y) -> AreEqual b y
sameDomainCo (FF z w) = w


--[ EOF ]
