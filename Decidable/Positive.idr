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
Not (D p n no)
  = D n p (negSym no)

public export
Swap : Decidable -> Decidable
Swap d
  = D d.Negative d.Positive (negSym d.Cancelled)


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
force : Positive.Dec this
     -> Either (this.Negative) (this.Positive)
force x {this} with 0 (this)
  force x {this} | (D positive negative cancelled) = x

public export
not : Positive.Dec this
   -> Positive.Dec (Not this)
not x with 0 (this) -- required to unroll things
  not (Left x) | (D positive negative cancelled) = Right x
  not (Right x) | (D positive negative cancelled) = Left x

-- [ EOF ]
