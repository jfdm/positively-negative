module Examples.Elab.STLC

import Data.Either
import Data.Singleton

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.String
import Decidable.Positive.Nat
import Decidable.Positive.Pair
import Decidable.Positive.List.Assoc
import Decidable.Positive.List.Elem
import Decidable.Positive.List.ElemAt
import Decidable.Positive.List.Quantifier
import Decidable.Positive.List.Quantifier

import Examples.Context
import Examples.Elab.STLC.Types

%default total

namespace STLC

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


  mutual
    namespace Synth
      public export
      data Error : (ctxt : Context Ty types)
                        -> Type
        where
          NotBound : {ctxt : Context Ty types}
                  -> (str : String)
                  -> (prf : Negative (ISBOUND str ctxt))
                         -> Error ctxt
          Next : Error (x :: xs) -> Error xs
          FuncExpected : (ty : Ty) -> Negative (ISFUNC ty) -> Error ctxt
          CheckError : (ty : Ty) -> Check.Error ctxt ty -> Error ctxt

    namespace Check
      public export
      data Error : (ctxt : Context Ty types)
                -> (type : Ty)
                        -> Type
        where
          SynthError : Synth.Error ctxt -> Error ctxt typeE
          Mismatch : (tyG : Ty)
                  -> (prf : Negative $ EQUAL tyG ty)
                         -> Error ctxt ty

  export
  synth : (ctxt : Context Ty types)
       -> (ast  : AST)
                -> Either (Synth.Error ctxt)
                          (DPair Ty (STLC  types))

  export
  check : (ctxt : Context Ty types)
       -> (ty   : Ty)
       -> (ast  : AST)
               -> Either (Check.Error ctxt  ty)
                         (STLC  types ty)
  check ctxt ty ast with (synth ctxt ast)
    check ctxt ty ast | (Left err)
      = Left (SynthError err)
    check ctxt ty ast | (Right (syn ** tm)) with (decEq' syn ty)
      check ctxt ty ast | (Right (syn ** tm)) | (Left err)
        = Left (Mismatch syn err)
      check ctxt ty ast | (Right (ty ** tm)) | (Right Refl) = Right tm

  synth ctxt (Var str)
    = case isBound str ctxt of
        (Left x) => Left (NotBound str x)
        (Right prf) =>
          case loc prf of
            (natLoc ** prf) =>
              case deBruijn prf of
                (ty ** loc)
                  => Right (ty ** V loc)

  synth ctxt (Func str ty expr)
    = case synth (I str (Val ty) :: ctxt) expr of
         Left err => Left (Next err)
         Right (tyRet ** tm) => pure (FUNC ty tyRet ** F tm)

  synth ctxt (App f a) with (synth ctxt f)
    synth ctxt (App f a) | (Left err) = Left err
    synth ctxt (App f a) | (Right (NAT ** ftm))
      = Left (FuncExpected NAT YIN)
    synth ctxt (App f a) | (Right ((FUNC x y) ** ftm)) with (check ctxt x a)
      synth ctxt (App f a) | (Right ((FUNC x y) ** ftm)) | (Left err)
        = Left (CheckError x err)
      synth ctxt (App f a) | (Right ((FUNC x y) ** ftm)) | (Right atm)
        = Right (y ** A ftm atm)

  synth ctxt (Nat k)
    = pure (NAT ** N k)

  synth ctxt (Add x y) with (check ctxt NAT x)
    synth ctxt (Add x y) | (Left err)
      = Left (CheckError NAT err)
    synth ctxt (Add x y) | (Right xtm) with (check ctxt NAT y)
      synth ctxt (Add x y) | (Right xtm) | (Left err)
        = Left (CheckError NAT err)
      synth ctxt (Add x y) | (Right xtm) | (Right ytm)
        = Right (NAT ** P xtm ytm)

  mutual
    namespace Synth
      export
      show : Error ctxt -> String
      show (NotBound str prf)
          = "\{str} is not bound"

      show (Next x)
          = show x

      show (FuncExpected ty x)
          = "Given:\n\t\{show ty}\n Expected a function"

      show (CheckError ty x)
          = show x

    namespace Check
      export
      show : {ty : Ty} -> Error ctxt ty -> String
      show (SynthError x)
        = show x
      show (Mismatch tyG prf) {ty}
        = "Given:\n\t\{show tyG}\n Expected\n\t\{show ty}"

  export
  elab : (ast : AST) -> Either (Error Nil) (DPair Ty (STLC Nil))
  elab = synth Nil

  export
  elabShow : (ast : AST) -> String
  elabShow ast = either show
                        (const $ "yes")
                        (elab ast)

-- [ EOF ]
