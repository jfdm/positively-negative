module Decidable.Positive.List.Assoc

import        Decidable.Positive
import        Decidable.Positive.Equality

import public Decidable.Positive.Pair
import public Decidable.Positive.List.Quantifier.Any

%default total

public export
HASKEY : (p  : key -> Decidable)
      -> (xs : List (key,value))
            -> Decidable
HASKEY p
  = Quantify.ANY (ONFIRST p)


export
hasKey : {p  : key -> Decidable}
      -> (f  : (k : key) -> Positive.Dec (p k))
      -> (xs : List (key,value))
            -> Positive.Dec (HASKEY p xs)
hasKey f
  = any (onFirst f)


public export
HOLDBOTH : (f : key   -> Decidable)
        -> (s : value -> Decidable)
        -> (p : List (key,value))
             -> Decidable
HOLDBOTH f s
  = Quantify.ANY (BOTH f s)

export
holdBoth : (f   : (x : key)   -> Positive.Dec (k x))
        -> (g   : (x : value) -> Positive.Dec (v x))
        -> (kvs : List (key,value))
               -> Positive.Dec (HOLDBOTH k v kvs)
holdBoth f g
  = Quantify.any (both f g)

public export
HOLDAT : Positive.DecEq key
      => (k   : key)
      -> (s   : value -> Decidable)
      -> (kvs : List (key,value))
             -> Decidable
HOLDAT k
  = HOLDBOTH (DECEQ k)

export
holdAt : Positive.DecEq key
      => (f   : (v : value) -> Positive.Dec (p v))
      -> (k   : key)
      -> (kvs : List (key,value))
             -> Positive.Dec (HOLDAT k p kvs)
holdAt f k
  = holdBoth (decEq k) f


public export
EXISTS : Positive.DecEq key
      => Positive.DecEq value
      => (k   : key)
      -> (s   : value)
      -> (kvs : List (key,value))
             -> Decidable
EXISTS k s
  = HOLDBOTH (DECEQ k) (DECEQ s)

export
exists : Positive.DecEq key
      => Positive.DecEq value
      => (k   : key)
      -> (v   : value)
      -> (kvs : List (key,value))
             -> Positive.Dec (EXISTS k v kvs)
exists k v
  = holdBoth (decEq k) (decEq v)


-- [ EOF ]
