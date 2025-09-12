||| Using decisions for the SLTC
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Elab.LSTLC

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.List.HoldsAt

import Examples.Context

%default total

namespace STLC

  public export
  data AST = Var String
           | Let String AST AST
           | Z | S AST
           | True | False
           | Add AST AST
           | And AST AST

namespace Usage
  public export
  data Usage = FREE | USED

  public export
  data EQU : (a,b : Usage) -> Type where
    FF : EQU FREE FREE
    UU : EQU USED USED

  public export
  data EQN : (a,b : Usage) -> Type where
    FU : EQN FREE USED
    UF : EQN USED FREE

  sym : EQN a b -> EQN b a
  sym FU = UF
  sym UF = FU

  public export
  ISFREE : Usage -> Decidable
  ISFREE u = D (EQU FREE u) (EQU USED u) prf
    where
      prf : forall u . EQU FREE u -> EQU USED u -> Void
      prf FF FF impossible
      prf FF UU impossible

  public export
  ISUSED : Usage -> Decidable
  ISUSED u = Swap (ISFREE u)

  export
  isFree : (u : Usage) -> Dec (ISFREE u)
  isFree FREE = Right FF
  isFree USED = Left UU

  export
  isUsed : (u : Usage) -> Dec (ISUSED u)
  isUsed u = mirror (isFree u)

  public export
  DecEQ Usage where
    EQUAL a b = D (EQU a b) (EQN a b) prf
      where
        prf : forall a,b . EQU a b -> EQN a b -> Void
        prf FF FU impossible
        prf FF UF impossible
        prf UU FU impossible
        prf UU UF impossible

    toRefl FF = Refl
    toRefl UU = Refl

    toVoid FU Refl impossible
    toVoid UF Refl impossible

    decEq FREE FREE = Right FF
    decEq FREE USED = Left FU
    decEq USED FREE = Left UF
    decEq USED USED = Right UU

    refl FREE = FF
    refl USED = UU


namespace Ty
  public export
  data Ty = NAT | BOOL

  public export
  data EQN : (a,b : Ty) -> Type where
    NB : EQN NAT  BOOL
    BN : EQN BOOL NAT

  public export
  data EQT : (a,b : Ty) -> Type where
    NN : EQT NAT  NAT
    BB : EQT BOOL BOOL

  public export
  DecEQ Ty where
    EQUAL a b = D (EQT a b) (EQN a b) prf
      where
        prf : forall a,b . EQT a b -> EQN a b -> Void
        prf NN NB impossible
        prf NN BN impossible
        prf BB NB impossible
        prf BB BN impossible

    toRefl NN = Refl
    toRefl BB = Refl

    toVoid BN Refl impossible
    toVoid NB Refl impossible

    decEq NAT NAT = Right NN
    decEq NAT BOOL = Left NB
    decEq BOOL NAT = Left BN
    decEq BOOL BOOL = Right BB

    refl NAT = NN
    refl BOOL = BB

namespace Item

  public export
  data Item = I Ty Usage

  public export
  data HasUsage : (Decidable -> Type) -> Usage -> Item -> Type where
    HU : pol (EQUAL a b) -> HasUsage pol a (I ty b)

  public export
  HASUSAGE : Usage -> Item-> Decidable
  HASUSAGE u i
    = D (HasUsage Positive u i)
        (HasUsage Negative u i)
        prf

    where
      0
      prf : forall u,i . HasUsage Positive u i
                      -> HasUsage Negative u i
                      -> Void
      prf {u} {i = I ty v} (HU pU) (HU nU)
        = (EQUAL u v).Cancels pU nU

  export
  hasUsage : (u : Usage)
          -> (i : Item)
               -> Dec (HASUSAGE u i)
  hasUsage u (I ty v)
    = do prf <- decEq u v `otherwise` HU
         pure (HU prf)


  public export
  FREEAT : String -> Context Item types -> DDecidable
  FREEAT str ctxt
    = HOLDSFOR str (HASUSAGE FREE) ctxt

  export
  freeAt : {types : _}
        -> (s : String)
        -> (ctxt : Context Item types)
        -> DDec (FREEAT s ctxt)
  freeAt
    = holdsFor (hasUsage FREE)

namespace Shift
  public export
  data Shift : (old : List Item)
            -> (pF : AtIndex (I ty FREE) old n)
            -> (new : List Item)
            -> (pU : AtIndex (I ty USED) new n)
             -> Type
    where
      Here : {xs : _}
          -> Shift (I ty FREE::xs) Z
                   (I ty USED::xs) Z

      There : (ltr : Shift  os oltr  ns nltr)
                  -> Shift (o::os) (S oltr)
                           (o::ns) (S nltr)

  public export
  data TheShift : (ctxt : Context Item old) -> (idx : Nat)
                        -> Type
    where
      R :  {old : _}
        -> {octxt : Context Item old}
        -> (ty  : Ty)
        -> (pF : AtIndex (I ty FREE) old idx)
        -> (new : List Item)
        -> (nctxt : Context Item new)
        -> (pU : AtIndex (I ty USED) new idx)
        -> (prf : Shift old pF new pU)
                -> TheShift octxt idx

  export
  shift : {types : List Item}
       -> (old : Context Item types)
       -> (prf : HoldsAt Item
                         (HOLDS (EQUAL str)
                                (HASUSAGE FREE)
                         )
                         old
                         idx)
              -> TheShift old idx
  shift {types=t::ts} (x :: xs) (Here prf) with (prf)
    shift {types=(I x y)::ts} ((I key (Val (I x y))) :: xs) (Here prf) | (H prfK (HU z)) with (z)
      shift {types=(I x FREE)::ts} ((I key (Val (I x FREE))) :: xs) (Here prf) | (H prfK (HU z)) | FF
        = R x Z (I x USED::ts) (I key (Val (I x USED)) :: xs) Z Here

  shift {types=t::ts} (x :: xs) (There tail) with (shift xs tail)
    shift {types=t::ts} (x :: xs) (There tail) | (R ty pF new nctxt pU prf)
      = R ty (S pF) (t::new) (x :: nctxt) (S pU) (There prf)

public export
data STLC : (old : List Item)
         -> Ty
         -> (new : List Item)
         -> Type
  where
    Var : (n : Nat)
       -> (0 pF : AtIndex (I ty FREE) old n)
       -> (0 pU : AtIndex (I ty USED) new n)
       -> (0 mv : Shift old pF new pU)
               -> STLC old ty new

    Let : (this  : STLC a ty b)
       -> (scope : STLC (I ty FREE :: b) tyb c)
                -> STLC a tyb c

    Z : STLC a NAT a

    True,False : STLC a BOOL a

    S : STLC a NAT b
     -> STLC a NAT b

    Add : STLC a NAT b
       -> STLC b NAT c
       -> STLC a NAT c

    And : STLC a BOOL b
       -> STLC b BOOL c
       -> STLC a BOOL c

mutual
  namespace Synth
    public export
    data Error : Type
      where
        Chk : (ty : Ty) -> Error ty -> Error
        ErrUsage : (ctxt : Context Item types)
                -> (str : String)
                -> (prf : (NEGATIVE (FREEAT str ctxt)))
                       -> Error

  namespace Check
    public export
    data Error : (ty : Ty)
              -> Type
      where
        Syn : (exp : Ty) -> Error -> Error exp

        Mismatch : (prf : Negative $ EQUAL giv ex)
                -> Error ex

namespace Synth
  public export
  data Result : (types : List Item)
             -> Type
    where
      R : {new : _}
       -> (ctxt : Context Item new)
       -> (type : Ty)
       -> (tm   : STLC old type new)
               -> Result old

namespace Check
  public export
  data Result : (types : List Item)
             -> (ty    : Ty)
             -> Type
    where
      R : {new : _}
       -> (ctxt : Context Item new)
       -> (tm   : STLC old type new)
               -> Result old type

synth : {types : _}
     -> (ctxt : Context Item types)
     -> (ast  : AST)
             -> Either (Error)
                       (Result types)

check : {types : _}
     -> (ctxt : Context Item types)
     -> (ty   : Ty)
     -> (ast  : AST)
             -> Either (Error ty)
                       (Result types ty)
check ctxt exp ast
  = do R new syn tm <- synth ctxt ast `otherwise` (Syn exp)
       Refl <- decEq' syn exp `otherwise` (Mismatch)
       pure (R new tm)

synth ctxt Z
  = pure $ R ctxt NAT Z

synth ctxt True
  = pure $ R ctxt BOOL True

synth ctxt False
  = pure $ R ctxt BOOL False

synth ctxt (S x)
  = do R new tm <- check ctxt NAT x `otherwise` (Chk NAT)
       pure $ R new NAT tm

synth ctxt (Add x y)
  = do R new  tx <- check ctxt NAT x `otherwise` (Chk NAT)
       R newn ty <- check new  NAT y `otherwise` (Chk NAT)
       pure $ R newn NAT (Add tx ty)

synth ctxt (And x y)
  = do R new  tx <- check ctxt BOOL x `otherwise` (Chk BOOL)
       R newn ty <- check new  BOOL y `otherwise` (Chk BOOL)
       pure $ R newn BOOL (And tx ty)

synth ctxt (Let str this scope)
  = do R new  ty  this <- synth ctxt this
       R newn tys scope <- synth (I str (Val $ I ty FREE)::new) scope
       pure $ R newn tys (Let this scope)

synth ctxt (Var str)
  = do (loc ** prf) <- freeAt str ctxt `otherwise` (ErrUsage ctxt str)
       let R ty pF _ new pU pShift = shift ctxt prf
       pure $ R new ty (Var loc pF pU pShift)


export
elab : (ast : AST) -> Either Error (Result Nil)
elab = synth Nil

exampleAST0 : AST
exampleAST0
  = Let "foo" True
  $ Let "bar" Z
  $ Add (Var "bar") (Var "bar")

exampleAST1 : AST
exampleAST1
  = Let "foo" True
  $ Let "bar" Z
  $ Add Z (Var "foo")

exampleAST2 : AST
exampleAST2
  = Let "foo" True
  $ Let "bar" Z
  $ Add Z (Var "fo")

exampleAST3 : AST
exampleAST3
  = Let "foo" Z
  $ Let "bar" (Var "foo")
  $ Add Z (Var "bar")

exampleTm1 : STLC Nil NAT ?as
exampleTm1
  = Let True
  $ Let Z
  $ Add Z (Var 0 Z Z Here)

exampleTm2 : STLC Nil NAT ?catzt
exampleTm2
  = Let True
  $ Let Z
  $ Let (S Z)
  $ Add (Var 0 Z Z Here)
        (Var 1 (S Z) (S Z) (There Here))

{-

  export
  elabShow : (ast : AST) -> String
  elabShow ast = either show
                        (const $ "yes")
                        (elab ast)
-}
-- [ EOF ]
