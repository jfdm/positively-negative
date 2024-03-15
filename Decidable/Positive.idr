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
Show (D p n _)
  = (Show p, Show n)

export
negSym : (no  : p -> n -> Void)
            -> (n -> p -> Void)
negSym no x y = no y x

public export
Not : Decidable -> Decidable
Not (D p q no)
  = D q p (negSym no)

||| This function is entirely Bob's idea.
public export
0
Dec : Decidable -> Type
Dec (D p q no)
  = Either q p

public export
data Decide : (d : Decidable) -> Positive.Dec d -> Type where
  Neg : Decide (D p q no) (Left v)
  Pos : Decide (D p q no) (Right v)

public export
decide : (res : Positive.Dec d)
             -> Decide d res
decide {d} res with 0 (d)
  decide {d = d} (Left x) | (D p n c) = Neg
  decide {d = d} (Right x) | (D p n c) = Pos

public export
decideE : (res : Positive.Dec d)
              -> Either (Negative d) (Positive d)
decideE {d} res with 0 (d)
  decideE {d = d} (Left x) | (D p n c) = Left x
  decideE {d = d} (Right x) | (D p n c) = Right x

public export
decidable : (value   : Positive.Dec d)
         -> (goLeft  : Lazy (Negative d -> a))
         -> (goRight : Lazy (Positive d -> a))
                    -> a
decidable value goLeft goRight with (decide value)
  decidable (Left v) goLeft goRight | Neg
    = goLeft v
  decidable (Right v) goLeft goRight | Pos
    = goRight v

public export
decidableE : (value   : Positive.Dec d)
          -> (goLeft  : Lazy (Negative d -> a))
          -> (goRight : Lazy (Positive d -> a))
                    -> a
decidableE value goLeft goRight
  = either goLeft goRight (decideE value)

show : (prfS : Show d)
     => (prf : Positive.Dec d)
           -> String
show prf with (decide prf)
  show (Left v) | Neg = Prelude.show v
  show (Right v) | Pos = Prelude.show v

export
Show d => Show (Positive.Dec d) where
  show x = Positive.show x




-- [ EOF ]
