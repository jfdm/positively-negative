||| Decidable equality of builtins.
|||
||| For builtins, we do not have access to their internal
||| implementations. We use `believe_me` because we don't them to
||| reduce and we need these things to type check.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Builtin.Equality

import        Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.Builtin

%default total

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
