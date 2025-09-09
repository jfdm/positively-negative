module Decidable.Positive.Builtin

import public Data.So

import Decidable.Positive

import public Decidable.Positive.So
import        Decidable.Positive.Equality

%default total

namespace Unary
  public export
  data PrimUnOp : (pol  : Decidable -> Type)
               -> (type : Type)
               -> (op   : type -> Bool)
               -> (p    : type)
                       -> Type
    where
      R : (prf : pol (SO (op p)))
                 -> PrimUnOp pol t op p

  public export
  PRIMUNOP : {type : Type}
          -> (op : type -> Bool)
          -> (s  : type)
                -> Decidable
  PRIMUNOP op s
      = D (PrimUnOp Positive type op s)
          (PrimUnOp Negative type op s)
          isVoid
    where
      0
      isVoid : PrimUnOp Positive type op p
            -> PrimUnOp Negative type op p
            -> Void
      isVoid (R prf) (R x)
        = (Cancelled (SO $ op p)) prf x

  export
  primUnOp : (op : type -> Bool)
          -> (s  : type)
                -> Dec (PRIMUNOP op s)
  primUnOp op s
    = either (Left . R)
             (Right . R)
             (isTrue (op s))

namespace Binary
  public export
  data PrimBinOp : (Decidable -> Type)
                -> (a : Type)
                -> (f : (x,y : a) -> Bool)
                -> (x,y : a)
                       -> Type
    where
      BinOpRes : (prf : t (SO (op x y))) -> PrimBinOp t a op x y


  public export
  PRIMBINOP : {type : Type}
           -> (op   : (x,y : type) -> Bool)
           -> (x,y  : type)
                   -> Decidable
  PRIMBINOP op x y
      = D (PrimBinOp Positive type op x y)
          (PrimBinOp Negative type op x y)
          isVoid
    where
      0
      isVoid : PrimBinOp Positive type op x y
            -> PrimBinOp Negative type op x y
            -> Void
      isVoid (BinOpRes prfP) (BinOpRes prfN)
        = (SO $ op x y).Cancelled prfP prfN

  export
  primBinOp : (op  : (x,y : type) -> Bool)
           -> (x,y : type)
                  -> Dec (PRIMBINOP op x y)
  primBinOp op x y
    = either (Left . BinOpRes)
             (Right . BinOpRes)
             (isTrue (op x y))



namespace Equality
  public export
  [Builtin] {a : Type} -> Eq a => DecEQ a where
    EQUAL = PRIMBINOP (==)

    toRefl (BinOpRes prf) = believe_me (Refl {x})

    toVoid (BinOpRes prf) Refl
      = believe_me {b = Void} ()

    decEq = primBinOp (==)

    refl this
      = BinOpRes {t=Positive} {x=this} {y=this}
                 (believe_me $ Data.So.Oh)


  --------------------------------------------------------------------------------
  -- Int
  --------------------------------------------------------------------------------

  public export
  DecEQ Int where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Bits8
  --------------------------------------------------------------------------------

  public export
  DecEQ Bits8 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Bits16
  --------------------------------------------------------------------------------

  public export
  DecEQ Bits16 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Bits32
  --------------------------------------------------------------------------------

  public export
  DecEQ Bits32 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Bits64
  --------------------------------------------------------------------------------

  public export
  DecEQ Bits64 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Int8
  --------------------------------------------------------------------------------

  public export
  DecEQ Int8 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Int16
  --------------------------------------------------------------------------------

  public export
  DecEQ Int16 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Int32
  --------------------------------------------------------------------------------

  public export
  DecEQ Int32 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Int64
  --------------------------------------------------------------------------------

  public export
  DecEQ Int64 where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Char
  --------------------------------------------------------------------------------
  public export
  DecEQ Char where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- Integer
  --------------------------------------------------------------------------------
  public export
  DecEQ Integer where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

  --------------------------------------------------------------------------------
  -- String
  --------------------------------------------------------------------------------
  public export
  DecEQ String where
      EQUAL  = EQUAL  @{Builtin}
      toRefl = toRefl @{Builtin}
      toVoid = toVoid @{Builtin}
      decEq  = decEq  @{Builtin}
      refl   = refl   @{Builtin}

-- [ EOF ]
