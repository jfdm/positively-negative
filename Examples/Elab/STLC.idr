module Examples.Elab.STLC

import Data.Either
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

  export
  Show Ty where
    show NAT = "Nat"
    show (FUNC a b) = "(\{show a} -> \{show b})"

  public export
  data AreEqual : Ty -> Ty -> Type where
    NN : AreEqual NAT NAT
    FF : AreEqual x a -> AreEqual y b -> AreEqual (FUNC x y) (FUNC a b)


  symEQ : STLC.AreEqual a b -> STLC.AreEqual b a
  symEQ NN = NN
  symEQ (FF x y) = FF (symEQ x) (symEQ y)

  public export
  data AreEqualNot : Ty -> Ty -> Type where
    NF : AreEqualNot NAT (FUNC x y)
    FN : AreEqualNot (FUNC x y) NAT
    FA : AreEqualNot x a -> AreEqualNot (FUNC x y) (FUNC a b)
    FR : AreEqualNot y b -> AreEqualNot (FUNC x y) (FUNC a b)

  helper : (e,f : Ty) -> String
  helper e f
    = "Expected:\n\n\{show e}\n\nbut given:\n\n\{show f}"


  show : {x,y : Ty} -> (STLC.AreEqualNot x y) -> String
  show {x = NAT} {y = (FUNC x y)} NF
    = helper NAT (FUNC x y)

  show {x = (FUNC x y)} {y = NAT} FN
    = helper NAT (FUNC x y)

  show {x = (FUNC x y)} {y = (FUNC a b)} (FA z)
    = "\{helper (FUNC x y) (FUNC a b)}\n\nSpecifically, the argument type differs:\n\n\{STLC.show z}"

  show {x = (FUNC x y)} {y = (FUNC a b)} (FR z)
    = "\{helper (FUNC x y) (FUNC a b)}\n\nSpecifically, the return type differs:\n\n\{STLC.show z}"

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

  isNeg : STLC.AreEqualNot x y
       -> Equal x y
       -> Void
  isNeg (FA z) Refl with (isNeg z)
    isNeg (FA z) Refl | boom
      = boom Refl
  isNeg (FR z) Refl with (isNeg z)
    isNeg (FR z) Refl | boom
      = boom Refl

  public export
  Positive.DecEq Ty where
    POS = AreEqual
    NEG = AreEqualNot

    VOID = isVoid

    toRefl = isEq
    toVoid = isNeg
    toReflInEq = isEq
    toVoidInEq = isNeg

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

  export
  showTM : STLC ctxt ty -> String
  showTM _ = "urgh"

  export
  showTM' : DPair Ty (STLC ctxt) -> String
  showTM' _ = "urgh"

  public export
  data Error : Type where
    Mismatch : {x,y : Ty} -> Positive (DECEQIN x y) -> Error
    FuncExpected : Ty -> Error
    NotBound : String -> Error

  export
  Show Error where
    show (Mismatch z)
      = "Type Mismatch\n\n\{STLC.show z}"
    show (FuncExpected x)
      = "Function expected, but found:\n\n\{show x}\n"

    show (NotBound str)
      = "Not bound: \{str}"

  compare : (x,y : Ty) -> Either Error
                                 (x = y)
  compare x y with (decEqN x y)
    compare x y | (Left z)
      = pure $ toRefl z
    compare x y | (Right z)
      = Left (Mismatch z)


  synth :  (ctxt : Context Ty types)
        -> (ast  : AST)
                -> Either Error
                          (DPair Ty (STLC types))

  check : (ctxt : Context Ty types)
       -> (ty   : Ty)
       -> (ast  : AST)
               -> Either Error
                         (STLC types ty)
  check ctxt tyE ast
    = do (tyF ** tm) <- synth ctxt ast
         Refl <- compare tyE tyF
         pure tm

  synth ctxt (Var str)
    = case isBound str ctxt of
        (Left x) => Left (NotBound str)
        (Right x) =>
          case loc x of
            (fst ** snd) => case deBruijn snd of
                                 ((y ** z)) => Right (_ ** V z)

  synth ctxt (Func str ty y)
    = do (tyP ** y) <- synth (I str (Val ty) :: ctxt) y
         pure (FUNC ty tyP ** F y)

  synth ctxt (App x y)
    = do (FUNC tyx tyy ** x) <- synth ctxt x
           | (ty ** x) => Left (FuncExpected ty)

         y <- check ctxt tyx y

         pure (tyy ** A x y)

  synth ctxt (Nat k)
    = pure (NAT ** N k)

  synth ctxt (Add x y)
    = do x <- check ctxt NAT x
         y <- check ctxt NAT y
         pure (NAT ** P x y)

  export
  elab : (ast : AST) -> Either Error (DPair Ty (STLC Nil))
  elab = synth Nil

  export
  elabShow : (ast : AST) -> String
  elabShow ast = either show
                        (showTM')
                        (elab ast)
-- [ EOF ]
