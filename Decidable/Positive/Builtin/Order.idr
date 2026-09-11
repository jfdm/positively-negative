||| Decidable equality of builtins.
|||
||| For builtins, we do not have access to their internal
||| implementations. We use `believe_me` because we don't them to
||| reduce and we need these things to type check.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Builtin.Order

import        Decidable.Positive

import public Decidable.Positive.Equality
import public Decidable.Positive.Order

import public Decidable.Positive.Bool

import public Decidable.Positive.Builtin
import public Decidable.Positive.Builtin.Equality

%default total

%inline 0
prf : Ord type
   => {0 x,y : type}
   -> So (x <= y)
   -> So (y > x)
   -> Void
prf _ _ = believe_me ()

LTE : Ord type
   => (x,y : type) -> Decidable
LTE x y = D (So (x <= y))
            (So (y > x))
            prf

public export
[Builtin] {a : Type} -> Ord a => DecEQ a => DecORD a where
  LTE x y = Order.LTE x y

  isRefl _ = believe_me $ Refl {x}

  isSymAnti _ _ = believe_me $ Refl {x}

  isTrans ab bc = believe_me $ Refl {x}

  decLTE x y
    = case x <= y of
        True => Right $ believe_me Data.So.Oh
        False => Left $ believe_me Data.So.Oh

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------

public export
Ord Int => DecORD Int where
    LTE       = LTE       @{Builtin}
    isRefl    = isRefl    @{Builtin}
    isSymAnti = isSymAnti @{Builtin}
    isTrans   = isTrans   @{Builtin}
    decLTE    = decLTE    @{Builtin}
{-
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
-}
-- [ EOF ]
