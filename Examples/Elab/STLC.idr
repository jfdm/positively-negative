module Examples.Elab.STLC

import Data.Singleton

import Decidable.Positive
import Decidable.Positive.String
import Decidable.Positive.Nat
import Decidable.Positive.Pair
import Decidable.Positive.List.Assoc
import Decidable.Positive.List.Elem
import Decidable.Positive.List.Quantifier.All
import Decidable.Positive.List.Quantifier.Any

import Examples.Context

%default total

namespace STLC
  public export
  data Ty = NAT | FUNC Ty Ty

  data AreEqual : Ty -> Ty -> Type where
    NN : AreEqual NAT NAT
    FF : AreEqual x a -> AreEqual y b -> AreEqual (FUNC x y) (FUNC a b)


  symEQ : STLC.AreEqual a b -> STLC.AreEqual b a
  symEQ NN = NN
  symEQ (FF x y) = FF (symEQ x) (symEQ y)

  data AreEqualNot : Ty -> Ty -> Type where
    NF : AreEqualNot NAT (FUNC x y)
    FN : AreEqualNot (FUNC x y) NAT
    FA : AreEqualNot x a -> AreEqualNot (FUNC x y) (FUNC a b)
    FR : AreEqualNot y b -> AreEqualNot (FUNC x y) (FUNC a b)

  symEQN : STLC.AreEqualNot a b -> STLC.AreEqualNot b a
  symEQN NF = FN
  symEQN FN = NF
  symEQN (FA x) = FA (symEQN x)
  symEQN (FR x) = FR (symEQN x)

  isVoid : AreEqual x y -> STLC.AreEqualNot x y -> Void
  isVoid NN NF impossible
  isVoid NN FN impossible
  isVoid NN (FA z) impossible
  isVoid NN (FR z) impossible

  isVoid (FF z v) (FA w) = isVoid z w
  isVoid (FF z v) (FR w) = isVoid v w

  isEq : STLC.AreEqual x y -> Equal x y
  isEq NN
    = Refl
  isEq (FF z w) with (isEq z)
    isEq (FF z w) | Refl with (isEq w)
      isEq (FF z w) | Refl | Refl = Refl

  isNeg : STLC.AreEqual x y
       -> STLC.AreEqualNot x y
       -> Equal x y
       -> Void
  isNeg NN NF Refl impossible
  isNeg NN FN Refl impossible
  isNeg NN (FA z) Refl impossible
  isNeg NN (FR z) Refl impossible

  isNeg (FF z v) (FA w) Refl = isNeg z w Refl
  isNeg (FF z v) (FR w) Refl = isNeg v w Refl

  export
  Positive.DecEq Ty where
    DECEQpos = AreEqual
    DECEQneg = AreEqualNot

    DECEQprf = isVoid

    DECEQeq = isEq

    DECEQeqn = isNeg

    decEq NAT NAT
      = Right NN
    decEq NAT (FUNC x y)
      = Left NF
    decEq (FUNC x z) NAT
      = Left FN
    decEq (FUNC x z) (FUNC y w) with (decEq x y)
      decEq (FUNC x z) (FUNC y w) | (Left v)
        = Left (FA v)
      decEq (FUNC x z) (FUNC y w) | (Right v) with (decEq z w)
        decEq (FUNC x z) (FUNC y w) | (Right v) | (Left s)
          = Left (FR s)
        decEq (FUNC x z) (FUNC y w) | (Right v) | (Right s)
          = Right (FF v s)

    decEqN x y = mirror (decEq x y)


  data AST = Var String
           | Func String AST
           | App AST AST
           | Nat Nat
           | Add AST AST

  data STLC : List Ty -> Ty -> Type
    where
      V : Positive (ELEM x xs)
       -> STLC xs s
      F : STLC (x::xs) y
       -> STLC     xs  (FUNC x y)

      A : STLC xs (FUNC x y)
       -> STLC xs       x
       -> STLC xs         y

      N : Nat -> STLC xs NAT
      P : (x,y : STLC xs NAT) -> STLC xs NAT

  data Item : Ty -> Type where
    I : String -> Singleton ty -> Item ty

export
deBruijn : Positive.DecEq type
        => (ctxt : All Item xs)
        -> Positive (ANY Item (HOLDS (DECEQ key) (DECEQ (the type value))) ctxt)
        -> Elem value xs
deBruijn (x :: xs) (Here prf) with (prf)
  deBruijn ((I key' (Val x)) :: xs) (Here prf) | (H (Same y) prfV) = ?as_rhs_1
deBruijn (x :: xs) (There prf tail) with (deBruijn xs tail)
  deBruijn (x :: xs) (There prf tail) | with_pat = There with_pat
