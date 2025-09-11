||| Decidable equality for builtins.
|||
||| The decisions here are not informative and mirrors how
||| it is down in Idris for such things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Builtin

import public Data.So

import Decidable.Positive

import public Decidable.Positive.So
import        Decidable.Positive.Equality

%default total

||| Making decisions about unary operators
namespace Unary

  ||| Uninformative, yet decidable, decision for whether
  ||| the given unary boolean operation `op` hold for `s`.
  |||
  ||| @op the unary operation being performed on values,
  |||     we expect positive decisions to be true and
  |||     negative ones to true.
  ||| @s  the value being reasoned about.
  |||
  export
  primUnOp : (op : type -> Bool)
          -> (s  : type)
                -> Dec (SO (op s))
  primUnOp op s
    = isTrue (op s)

namespace Binary
  ||| Encapslates both positive and negative decisions about
  ||| boolean binary operators.
  |||
  ||| @pol is the expected polarity of the outcome.
  |||      We require this to reduce the number of
  |||      datatypes we require.
  |||
  ||| @type the type of builtins, we require this later
  |||       when hooking into predefined interfaces
  public export
  data PrimBinOp : (pol  : Decidable -> Type)
                -> (type : Type)
                -> (op   : (x,y : type) -> Bool)
                -> (x,y  : type)
                       -> Type
    where
      BinOpRes : (prf : pol (SO (op x y))) -> PrimBinOp pol type op x y

  ||| Uninformative, yet decidable, decision for whether
  ||| the given unary boolean operation `op` hold for `s`.
  |||
  ||| @op the binary operation being performed on values,
  |||     we expect positive decisions to be true and
  |||     negative ones to true.
  ||| @p  the value being reasoned about.
  |||
  export
  primBinOp : (op  : (x,y : type) -> Bool)
           -> (x,y : type)
                  -> Dec (SO (op x y))
  primBinOp op x y
    = isTrue (op x y)

||| For builtins, we do not have access to their internal
||| implementations. We use `believe_me` because we don't them to
||| reduce and we need these things to type check.
namespace Equality
  public export
  [Builtin] {a : Type} -> Eq a => DecEQ a where
    EQUAL x y =  SO ((==) x y)

    toRefl _
      = believe_me (Refl {x})

    toVoid _ Refl
      = believe_me {b = Void} ()

    decEq x y
      = isTrueBlock $ (==) x y

    refl this
      = believe_me $ Data.So.Oh

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
