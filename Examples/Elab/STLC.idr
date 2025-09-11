||| Using decisions for the SLTC
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Elab.STLC

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
      V : (n : Nat)
       -> (0 prf : AtIndex s xs n)
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
                  -> (prf : (NEGATIVE (ISBOUNDAT str ctxt)))
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
  synth : {types : List Ty}
       -> (ctxt : Context Ty types)
       -> (ast  : AST)
                -> Either (Synth.Error ctxt)
                          (DPair Ty (STLC  types))

  export
  check : {types : List Ty}
       -> (ctxt  : Context Ty types)
       -> (ty    : Ty)
       -> (ast   : AST)
               -> Either (Check.Error ctxt ty)
                         (STLC  types ty)
  check ctxt ty ast
    = do (syn ** tm) <- synth ctxt ast `otherwise` SynthError
         Refl <- decEq' syn ty `otherwise` (Mismatch syn)
         pure tm

  synth ctxt (Var str)
    = do (loc ** prf) <- isBound str ctxt `otherwise` (NotBound str)
         let (ty ** idx) = toIndex prf
         pure (ty ** V loc idx)

  synth ctxt (Func str ty expr)
    = case synth (I str (Val ty) :: ctxt) expr of
         Left err => Left (Next err)
         Right (tyRet ** tm) => pure (FUNC ty tyRet ** F tm)

  synth ctxt (App f a)
    = do (FUNC x y ** ftm) <- synth ctxt f `otherwise` id
            | (NAT ** ftm) => Left (FuncExpected NAT YIN)
         atm <- check ctxt x a `otherwise` (CheckError x)
         pure (y ** A ftm atm)

  synth ctxt (Nat k)
    = pure (NAT ** N k)

  synth ctxt (Add x y)
    = do xtm <- check ctxt NAT x `otherwise` (CheckError NAT)
         ytm <- check ctxt NAT y `otherwise` (CheckError NAT)
         pure (NAT ** P xtm ytm)

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
