module Decidable.Positive.Pair

import public Decidable.Positive

%default total

namespace First
  public export
  data OnFirst : (pred : f -> Decidable)
              -> (pair : (f,s))
                      -> Type
    where
      H :  {0 kv : (type_f,type_s)}
        -> {0 p : type_f -> Decidable}
        -> (prf : Positive (p $ fst kv))
              -> OnFirst p kv

  0
  no : OnFirst         p  x
    -> OnFirst (Swap . p) x
    -> Void
  no {x=(f,s)} (H pY) (H pN)
    = (p f).Cancelled pY pN

  public export
  ONFIRST : (p : f -> Decidable) -> (x : (f,s)) -> Decidable
  ONFIRST p x
    = D (OnFirst         p  x)
        (OnFirst (Swap . p) x)
        no

  export
  onFirst : {0 p : type -> Decidable}
         -> (f  : (x : type) -> Positive.Dec (p x))
         -> (kv : (type,b))
              -> Positive.Dec (ONFIRST p kv)
  onFirst f kv
    = either (\r => Left (H r))
             (\r => Right (H r))
             (f (fst kv))

  public export
  ONFIRSTNOT : (p : f -> Decidable) -> (x : (f,s)) -> Decidable
  ONFIRSTNOT p x
    = Swap (ONFIRST p x)

  export
  onFirstNot : (f : (x : type) -> Positive.Dec (p x))
            -> (x : (type,b))
                 -> Positive.Dec (ONFIRSTNOT p x)
  onFirstNot f (x, y)
    = mirror (onFirst f (x,y))

namespace Second
  public export
  data OnSecond : (pred : s -> Decidable)
               -> (pair : (f,s))
                       -> Type
    where
      H : {0 p   : type_s -> Decidable}
       -> (  prf : Positive (p s))
                -> OnSecond p (f,s)

  0
  no : OnSecond         p  x
    -> OnSecond (Swap . p) x
    -> Void
  no (H pY) (H pN)
    = (p (snd x)).Cancelled pY pN

  public export
  ONSECOND : (p : s -> Decidable) -> (x : (f,s)) -> Decidable
  ONSECOND p x
    = D (OnSecond         p  x)
        (OnSecond (Swap . p) x)
        no

  export
  onSecond : (f : (x : type) -> Positive.Dec (p x))
          -> (x : (a,type))
               -> Positive.Dec (ONSECOND p x)
  onSecond f (x, y)
    = either (Left  . H)
             (Right . H)
             (f y)

  public export
  ONSECONDNOT : (p : s -> Decidable) -> (x : (f,s)) -> Decidable
  ONSECONDNOT p x
    = Swap (ONSECOND p x)

  export
  onSecondNot : (f : (x : type) -> Positive.Dec (p x))
            -> (x : (a,type))
                 -> Positive.Dec (ONSECONDNOT p x)
  onSecondNot f (x, y)
    = mirror (onSecond f (x,y))


namespace Both

  public export
  data Both : (f : typeF -> Decidable)
           -> (s : typeS -> Decidable)
           -> (p : Pair typeF typeS)
                 -> Type
    where
      B :      {0 f : ftype -> Decidable}
    -> {0 s : stype -> Decidable}
    -> (pF : Positive (f x))
       -> (pS : Positive (s y))
             -> Both f s (x,y)

  public export
  data BothNot : (f : typeF -> Decidable)
              -> (s : typeS -> Decidable)
              -> (p : Pair typeF typeS)
                    -> Type
    where
      FNot : {0 f : typeF -> Decidable}
          -> (pF  : Positive (f x))
                 -> BothNot f s (x,y)
      SNot : {0 s : typeF -> Decidable}
          -> (pS  : Positive (s y))
               -> BothNot f s (x,y)
      BNot : {0 f : ftype -> Decidable}
          -> {0 s : stype -> Decidable}
          -> (pF  : Positive (f x))
          -> (pS  : Positive (s y))
                 -> BothNot f s (x,y)

  0
  no : {0 p : Pair ftype stype}
    -> {0 f : ftype -> Decidable}
    -> {0 s : stype -> Decidable}
    -> Both            f          s  p
    -> BothNot (Swap . f) (Swap . s) p
    -> Void
  no (B pFY pSY) (FNot pFN)
    = (f $ fst p).Cancelled pFY pFN

  no (B pFY pSY) (SNot pSN)
    = (s $ snd p).Cancelled pSY pSN

  no (B pFY pSY) (BNot pFN pSN)
    = (f $ fst p).Cancelled pFY pFN

  public export
  BOTH : (f : typeF -> Decidable)
      -> (s : typeS -> Decidable)
      -> (p : Pair typeF typeS)
           -> Decidable
  BOTH f s p
    = D (Both            f          s  p)
        (BothNot (Swap . f) (Swap . s) p)
        no

  export
  both : {0 p : typeF -> Decidable}
      -> {0 q : typeS -> Decidable}
      -> (f : (x : typeF) -> Positive.Dec (p x))
      -> (g : (x : typeS) -> Positive.Dec (q x))
      -> (x : Pair typeF typeS)
           -> Positive.Dec (BOTH p q x)
  both f g (x, y) with (f x)
    both f g (x, y) | fres with (g y)
      both f g (x, y) | (Left pFN)  | (Left pSN)
        = Left (BNot pFN pSN)
      both f g (x, y) | (Left pFN)  | (Right pSY)
        = Left (FNot pFN)
      both f g (x, y) | (Right pFY) | (Left pSN)
        = Left (SNot pSN)
      both f g (x, y) | (Right pFY) | (Right pSY)
        = Right (B pFY pSY)

  public export
  BOTHNOT : (f : typeF -> Decidable)
         -> (s : typeS -> Decidable)
         -> (p : Pair typeF typeS)
              -> Decidable
  BOTHNOT f s p
    = Swap (BOTH f s p)

  export
  bothNot : (f : (x : typeF) -> Positive.Dec (p x))
         -> (g : (x : typeS) -> Positive.Dec (q x))
         -> (x : Pair typeF typeS)
              -> Positive.Dec (BOTHNOT p q x)
  bothNot f g (x, y)
    = mirror $ both f g (x,y)

-- [ EOF ]
