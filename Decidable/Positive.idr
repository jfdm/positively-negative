module Decidable.Positive

import public Data.Either

%default total

public export
record Decidable where
  constructor D
  Positive : Type
  Negative : Type
  0 Cancelled : Positive -> Negative -> Void

public export
Show : Decidable -> Type
Show d
  = (Show (d.Positive), Show (d.Negative))


||| This function is entirely Bob's idea.
public export
0
Dec : Decidable -> Type
Dec d
  = Either (d.Negative)
           (d.Positive)

show : (prfS : Show d)
     => (prf : Positive.Dec d)
           -> String
show (Left x) = Prelude.show x
show (Right x) = Prelude.show x

export
Show d => Show (Positive.Dec d) where
  show x = Positive.show x

public export
swap : (no  : p -> n -> Void)
          -> (n -> p -> Void)
swap no x y = no y x

public export
negSym : (no  : p -> n -> Void)
            -> (n -> p -> Void)
negSym no x y = no y x

public export
Not : Decidable -> Decidable
Not d = D (Negative d) (Positive d) (negSym (Cancelled d))

public export
Swap : Decidable -> Decidable
Swap = Not

public export
Mirror : Decidable -> Decidable
Mirror = Not

public export
not : Positive.Dec      this
   -> Positive.Dec (Not this)
not = mirror


{- [ NOTE ] Anti-pattern

public export
Not : Decidable -> Decidable
Not (D p n no)
  = D n p (negSym no)

public export
not : Positive.Dec this
   -> Positive.Dec (Not this)
not x with 0 (this) -- required to unroll things
  not (Left x) | (D positive negative cancelled) = Right x
  not (Right x) | (D positive negative cancelled) = Left x
-}
-- [ EOF ]
