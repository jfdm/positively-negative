module Decidable.Positive.List.Assoc

import        Decidable.Positive
import        Decidable.Positive.Dependent
import        Decidable.Positive.Equality

import public Decidable.Positive.Pair
import public Decidable.Positive.DPair
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
HOLDAT : DecEQ key
      => (k   : key)
      -> (s   : value -> Decidable)
      -> (kvs : List (key,value))
             -> Decidable
HOLDAT k
  = HOLDBOTH (EQUAL k)

export
holdAt : DecEQ key
      => (f   : (v : value) -> Positive.Dec (p v))
      -> (k   : key)
      -> (kvs : List (key,value))
             -> Positive.Dec (HOLDAT k p kvs)
holdAt f k
  = holdBoth (decEq k) f


public export
EXISTS : DecEQ key
      => DecEQ value
      => (k   : key)
      -> (s   : value)
      -> (kvs : List (key,value))
             -> Decidable
EXISTS k s
  = HOLDBOTH (EQUAL k) (EQUAL s)

export
exists : DecEQ key
      => DecEQ value
      => (k   : key)
      -> (v   : value)
      -> (kvs : List (key,value))
             -> Positive.Dec (EXISTS k v kvs)
exists k v
  = holdBoth (decEq k) (decEq v)


namespace Lookup

  public export
  data ByKey : (f : (x,y : key) -> Decidable)
            -> (pos : Decidable -> Type)
            -> (neg : Decidable -> Type)
            -> (k   : key)
            -> (v   : Maybe value)
            -> (kvs : List (Pair key value))
                   -> Type

    where
      Here : {0 f : (x,y : key) -> Decidable}
          -> (pK : pos (f x a))
                -> ByKey f pos neg x (Just b) ((a,b) :: kvs)

      There : {0 f : (x,y : key) -> Decidable}
           -> (pK  : neg (f x a))
            -> (ltr : ByKey f pos neg x y kvs)
                   -> ByKey f pos neg x y ((a,b) :: kvs)

  public export
  data ByKeyNot : (f : (x,y : key) -> Decidable)
               -> (pos : Decidable -> Type)
               -> (neg : Decidable -> Type)
               -> (k   : key)
               -> (v   : Maybe value)
               -> (kvs : List (Pair key value))
                      -> Type
    where
      Empty : ByKeyNot f pos neg x Nothing Nil

      Extend : {0 f   : (x,y : key) -> Decidable}
            -> (  pK  : pos (f x a))
            -> (  ltr : ByKeyNot f pos neg x y kvs)
                     -> ByKeyNot f pos neg x y ((a,b) :: kvs)

  0
  no : (v : Maybe value)
    -> ByKey    f Positive Negative k v kvs
    -> ByKeyNot f Negative Positive k v kvs
    -> Void
  no (Just b) (Here pK) (Extend x ltr) = (f k _).Cancelled pK x
  no v (There pK ltr) (Extend x y) = no v ltr y

  public export
  LOOKUP : {value : Type}
        -> DecEQ key
        => (k : key)
        -> (kvs : List (Pair key value))
               -> DDecidable
  LOOKUP k kvs
    = D _ (\v => ByKey    EQUAL Positive Negative k v kvs)
          (\v => ByKeyNot EQUAL Negative Positive k v kvs)
          no

  export
  lookup : DecEQ key
        => (k : key)
        -> (kvs : List (Pair key value))
               -> DDec (LOOKUP k kvs)
  lookup k [] = Left ((Nothing ** Empty))
  lookup k ((x,v) :: xs) with (decEq k x)
    lookup k ((x,v) :: xs) | (Left pN) with (lookup k xs)
      lookup k ((x,v) :: xs) | (Left pN) | (Left (fst ** snd))
        = Left (fst ** Extend pN snd)
      lookup k ((x,v) :: xs) | (Left pN) | (Right (fst ** snd))
        = Right (fst ** There pN snd)
    lookup k ((x,v) :: xs) | (Right pY)
      = Right (Just v ** Here pY)

  public export
  0
  no' : ByKey    f Positive Negative k v kvs
     -> ByKeyNot f Negative Positive k v kvs
     -> Void
  no' (Here pK) (Extend x ltr) = (f k _).Cancelled pK x
  no' (There pK ltr) (Extend x y) = no' ltr y

  public export
  ELEM : DecEQ key
      => (k : key)
      -> (v : value)
      -> (kvs : List (Pair key value))
             -> Decidable
  ELEM k v kvs
    = D (ByKey    EQUAL Positive Negative k (Just v) kvs)
        (ByKeyNot EQUAL Negative Positive k (Just v) kvs)
        no'

-- [ EOF ]
