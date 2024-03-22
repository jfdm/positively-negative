module Examples.Elab.STLC

import Data.Singleton

import Decidable.Positive
import Decidable.Positive.String
import Decidable.Positive.Nat
import Decidable.Positive.Pair
import Decidable.Positive.List.Assoc
import Decidable.Positive.List.Elem
import Decidable.Positive.List.ElemAt
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

  public export
  data AST = Var String
           | Func String Ty AST
           | App AST AST
           | Nat Nat
           | Add AST AST

  public export
  data STLC : List Ty -> Ty -> Type
    where
      V : AtIndex s xs n
       -> STLC xs s
      F : STLC (x::xs) y
       -> STLC     xs  (FUNC x y)

      A : STLC xs (FUNC x y)
       -> STLC xs       x
       -> STLC xs         y

      N : Nat -> STLC xs NAT
      P : (x,y : STLC xs NAT) -> STLC xs NAT

  public export
  data Error : Type where
    Mismatch : (x,y : Ty) -> Error
    FuncExpected : Ty -> Error
    NotBound : String -> Error

  export
  elab : (ctxt : Context Ty types)
       -> (ast  : AST)
               -> Either Error
                         (DPair Ty (STLC types))
  elab ctxt (Var str)
    = case isBound str ctxt of
        (Left x) => Left (NotBound str)
        (Right x) =>
          case loc x of
            (fst ** snd) => case deBruijn snd of
                                 ((y ** z)) => Right (_ ** V z)

  elab ctxt (Func str ty y)
    = do (tyP ** y) <- elab (I str (Val ty) :: ctxt) y
         pure (FUNC ty tyP ** F y)

  elab ctxt (App x y)
    = do (FUNC tyx tyy ** x) <- elab ctxt x
           | (ty ** x) => Left (FuncExpected ty)

         (tyy' ** y) <- elab ctxt y


         case decEq tyx tyy' of
           (Left z) => Left (Mismatch tyx tyy')
           (Right z) =>
             case isEq z of
               Refl => pure (tyy ** A x y)

  elab ctxt (Nat k)
    = pure (NAT ** N k)

  elab ctxt (Add x y)
    = do (NAT ** x) <- elab ctxt x
            | (ty ** x) => Left (Mismatch NAT ty)

         (NAT ** y) <- elab ctxt y
            | (ty ** y) => Left (Mismatch NAT ty)

         pure (NAT ** P x y)
