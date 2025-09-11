||| Decidable Decisions but without requiring void at runtime.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive

import public Data.Either

%default total

||| A description for decidable things.
|||
||| Two positive types are paired with a proof that the two positive
||| types cancel each other.
|||
public export
record Decidable where
  constructor D
  Positive : Type
  Negative : Type
  0 Cancels : Positive -> Negative -> Void

||| Informs us how to `Show` the outputs of a decision.
public export
Show : Decidable -> Type
Show d
  = (Show (d.Positive), Show (d.Negative))


||| Decisions whose outputs are positive can be revisited as `Either`.
|||
||| This function is entirely Bob's idea.
public export
0
Dec : Decidable -> Type
Dec d
  = Either (d.Negative)
           (d.Positive)

export
Show d => Show (Positive.Dec d) where
  show (Left x) = Prelude.show x
  show (Right x) = Prelude.show x

    -- Positive.show x

||| Proof that two things cancels each other is symmetric.
public export
swap : (no  : p -> n -> Void)
          -> (n -> p -> Void)
swap no x y = no y x

||| A more constructive alias for `swap`.
public export
negSym : (no  : p -> n -> Void)
            -> (n -> p -> Void)
negSym = swap

||| Swap the polarity of the decisions so that what is positive is now
||| negative, and vice-versa.
public export
Swap : Decidable -> Decidable
Swap d = D (Negative d) (Positive d) (swap (Cancels d))

||| A more constructive alias for `Swap`.
public export
Mirror : Decidable -> Decidable
Mirror = Swap

||| Helper function for making decisions along the 'happy path' in the
||| `Either` monad
public export
%inline
otherwise : Either inner_err a
         -> (inner_err -> outer_err)
         -> Either outer_err a
otherwise (Left  x) f = Left (f x)
otherwise (Right x) f = Right x

||| Helper function for making decisions along the 'sad path' in the
||| `Either` monad.
public export
%inline
wiseother : Either err inner_a
         -> (inner_a -> outer_a)
         -> Either outer_a err
wiseother (Left  x) f = Right x
wiseother (Right x) f = Left (f x)


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
