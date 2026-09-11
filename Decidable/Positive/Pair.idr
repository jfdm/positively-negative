||| Decidable things for Pairs
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Pair

import public Decidable.Positive
import public Decidable.Positive.Equality
import Decidable.Positive.Nat
%default total

||| Reasoning about the first element.
namespace First

  public export
  data OnFirst : (pred : f -> Decidable)
              -> (pair : (f,s))
                      -> Type
    where
      H : forall p
        . (prf : Positive (p x))
              -> OnFirst p (x,y)

  %inline 0
  no : OnFirst         p  (i,j)
    -> OnFirst (Swap . p) (i,j)
    -> Void
  no {i} (H pY) (H pN)
    = (p i).Cancels pY pN


  public export
  ONFIRST : (p : f -> Decidable) -> (t: (f,s)) -> Decidable
  ONFIRST p (x,y)
    = D (OnFirst         p  (x,y))
        (OnFirst (Swap . p) (x,y))
        no

  export
  onFirst : (d  : (x : f) -> Positive.Dec (p x))
         -> (fs : (f,s))
              -> Positive.Dec (ONFIRST p fs)
  onFirst f (x,y)
    = either (Left  . H)
             (Right . H)
             (f x)

  public export
  ONFIRSTNOT : (d : f -> Decidable) -> (x : (f,s)) -> Decidable
  ONFIRSTNOT p x
    = Swap (ONFIRST p x)

  export
  onFirstNot : (d : (x : f) -> Positive.Dec (p x))
            -> (x : (f,s))
                 -> Positive.Dec (ONFIRSTNOT p x)
  onFirstNot f (x, y)
    = mirror $ onFirst f (x,y)

namespace Second
  public export
  data OnSecond : (pred : s -> Decidable)
               -> (pair : (f,s))
                       -> Type
    where
      H : forall p
        . (prf : Positive (p s))
              -> OnSecond p (f,s)

  %inline 0
  no : OnSecond         p  x
    -> OnSecond (Swap . p) x
    -> Void
  no (H pY) (H pN)
    = (p (snd x)).Cancels pY pN

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
    = (ONSECOND (Swap . p) x)

  export
  onSecondNot : (f : (x : type) -> Positive.Dec (p x))
            -> (x : (a,type))
                 -> Positive.Dec (ONSECONDNOT p x)
  onSecondNot f (x, y)
    = (onSecond (\x => mirror $ f x) (x,y))


namespace Both

  public export
  data Both : (f : typeF -> Decidable)
           -> (s : typeS -> Decidable)
           -> (p : Pair typeF typeS)
                 -> Type
    where
      B : forall f, s
        . (pF : Positive (f x))
       -> (pS : Positive (s y))
             -> Both f s (x,y)

  public export
  data BothNot : (f : typeF -> Decidable)
              -> (s : typeS -> Decidable)
              -> (p : Pair typeF typeS)
                    -> Type
    where
      FNot : forall f
           . (pF  : Positive (f x))
                 -> BothNot f s (x,y)
      SNot : forall s
           . (pS  : Positive (s y))
               -> BothNot f s (x,y)
      BNot : forall f, s
           . (pF  : Positive (f x))
          -> (pS  : Positive (s y))
                 -> BothNot f s (x,y)

  %inline 0
  no : forall p, f, s
     . Both            f          s  p
    -> BothNot (Swap . f) (Swap . s) p
    -> Void
  no (B pFY pSY) (FNot pFN)
    = (f $ fst p).Cancels pFY pFN

  no (B pFY pSY) (SNot pSN)
    = (s $ snd p).Cancels pSY pSN

  no (B pFY pSY) (BNot pFN pSN)
    = (f $ fst p).Cancels pFY pFN

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
  both : (f : (x : typeF) -> Positive.Dec (p x))
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
