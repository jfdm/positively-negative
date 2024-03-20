module Decidable.Positive.Pair

import public Decidable.Positive
import public Decidable.Positive.Equality

%default total

namespace First
  public export
  data OnFirst : (pred : f -> Decidable)
              -> (pos  : Decidable -> Type)
              -> (neg  : Decidable -> Type)
              -> (pair : (f,s))
                      -> Type
    where
      Holds : {0 pred : type -> Decidable}
           -> (  prf  : pos (pred f))
                     -> OnFirst pred pos neg (f,s)

  0
  no : OnFirst p Positive Negative x
    -> OnFirst p Negative Positive x
    -> Void
  no {p = p} {x = (f, s)} (Holds y) (Holds n) with (p f)
    no {p = p} {x = (f, s)} (Holds y) (Holds n) | (D po ne cancelled)
      = cancelled y n

  public export
  ONFIRST : (p : f -> Decidable) -> (x : (f,s)) -> Decidable
  ONFIRST p x
    = D (OnFirst p Positive Negative x)
        (OnFirst p Negative Positive x)
        (no)

  export
  onFirst : (f : (x : type) -> Positive.Dec (p x))
         -> (x : (type,b))
              -> Positive.Dec (ONFIRST p x)
  onFirst f (x, y) with (decideE $ f x)
    onFirst f (x, y) | (Left z) = Left (Holds z)
    onFirst f (x, y) | (Right z) = Right (Holds z)


namespace Second
  public export
  data OnSecond : (pred : s -> Decidable)
              -> (pos  : Decidable -> Type)
              -> (neg  : Decidable -> Type)
              -> (pair : (f,s))
                      -> Type
    where
      Holds : {0 pred : type -> Decidable}
           -> (  prf  : pos (pred s))
                     -> OnSecond pred pos neg (f,s)

  0
  no : OnSecond p Positive Negative x
    -> OnSecond p Negative Positive x
    -> Void
  no {p = p} {x = (f, s)} (Holds y) (Holds n) with (p s)
    no {p = p} {x = (f, s)} (Holds y) (Holds n) | (D po ne cancelled)
      = cancelled y n

  public export
  ONSECOND : (p : s -> Decidable) -> (x : (f,s)) -> Decidable
  ONSECOND p x
    = D (OnSecond p Positive Negative x)
        (OnSecond p Negative Positive x)
        (no)

  export
  onSecond : (f : (x : type) -> Positive.Dec (p x))
         -> (x : (a,type))
              -> Positive.Dec (ONSECOND p x)
  onSecond f (x, y) with (decideE $ f y)
    onSecond f (x, y) | (Left z) = Left (Holds z)
    onSecond f (x, y) | (Right z) = Right (Holds z)

namespace Both

  public export
  data Both : (f : typeF -> Decidable)
           -> (s : typeS -> Decidable)
           -> (t : Decidable -> Type)
           -> (p : Pair typeF typeS)
                 -> Type
    where
      B : {0 f : typeF -> Decidable}
       -> {0 s : typeS -> Decidable}
       -> (pF : t (f x))
       -> (pS : t (s y))
             -> Both f s t (x,y)

  public export
  data BothNot : (f : typeF -> Decidable)
              -> (s : typeS -> Decidable)
              -> (t : Decidable -> Type)
              -> (p : Pair typeF typeS)
                    -> Type
    where
      BF : {0 f : typeF -> Decidable}
        -> (pF  : t (f x))
               -> BothNot f s t (x,y)
      BS : {0 f : typeF -> Decidable}
        -> (pS  : t (s y))
               -> BothNot f s t (x,y)
  0
  no : Both    f s Positive p
    -> BothNot f s Negative p
    -> Void
  no {p = (x, y)} {f = f} {s = s} (B pF pS) (BF nF) with (f x)
    no {p = (x, y)} {f = f} {s = s} (B pF pS) (BF nF) | (D po ne cancelled)
      = cancelled pF nF

  no {p = (x, y)} {f = f} {s = s} (B pF pS) (BS nS) with (s y)
    no {p = (x, y)} {f = f} {s = s} (B pF pS) (BS nS) | (D po ne cancelled)
      = cancelled pS nS

  public export
  BOTH : (f : typeF -> Decidable)
      -> (s : typeS -> Decidable)
      -> (p : Pair typeF typeS)
           -> Decidable
  BOTH f s p
    = D (Both    f s Positive p)
        (BothNot f s Negative p)
        no


  export
  both : (f : (x : typeF) -> Positive.Dec (p x))
      -> (g : (x : typeS) -> Positive.Dec (q x))
      -> (x : Pair typeF typeS)
           -> Positive.Dec (BOTH p q x)
  both f g (x, y) with (decideE $ f x)
    both f g (x, y) | (Left z) = Left (BF z)
    both f g (x, y) | (Right z) with (decideE $ g y)
      both f g (x, y) | (Right z) | (Left w)
        = Left (BS w)
      both f g (x, y) | (Right z) | (Right w)
        = Right (B z w)

-- [ EOF ]
