module Examples.Tree


import public Decidable.Positive
import public Decidable.Positive.Equality
import Decidable.Positive.Nat

%default total

data Tree a = Leaf | Node a (Tree a) (Tree a)


data All : (pred : (value : type) -> Decidable)
        -> (pos  : Decidable -> Type)
        -> (neg  : Decidable -> Type)
        -> (tree : Tree a)
                -> Type
  where
    Empty : All p pos neg Leaf
    Branch : {0 p : type -> Decidable}
          -> (prf : pos (p x))
          -> (prfL : All p pos neg left)
          -> (prfR : All p pos neg right)
                  -> All p pos neg (Node x left right)

data Any : (pred : (value : type) -> Decidable)
        -> (pos  : Decidable -> Type)
        -> (neg  : Decidable -> Type)
        -> (tree : Tree a)
                -> Type
  where
    Here : {0 p : type -> Decidable}
        -> (prf : pos (p x))
               -> Any p pos neg (Node x left right)

    ThereL : {0 p : type -> Decidable}
          -> (prf : neg (p x))
          -> (ltr : Any p pos neg left)
                 -> Any p pos neg (Node x left right)

    ThereR : {0 p : type -> Decidable}
          -> (prf : neg (p x))
          -> (ltr : Any p pos neg right)
                 -> Any p pos neg (Node x left right)

namespace ALL

  0
  prf : {t : Tree a} -> All p Positive Negative t
                     -> Any p Negative Positive t
                     -> Void
  prf Empty (Here x) impossible
  prf Empty (ThereL x ltr) impossible
  prf Empty (ThereR x ltr) impossible
  prf {p} {t=Node v l r} (Branch x prfL prfR) ant with (ant)
    prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (Here prfA) with (p v)
      prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (Here prfA) | (D positive negative cancelled)
        = cancelled x prfA
    prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (ThereL prfA ltr)
      = ALL.prf prfL ltr
    prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (ThereR prfA ltr)
      = ALL.prf prfR ltr

  public export
  ALL : (p : type -> Decidable) -> (t : Tree a) -> Decidable
  ALL p t = D (All p Positive Negative t)
              (Any p Negative Positive t)
              prf

  export
  all : (f : (x : a) -> Positive.Dec (p x))
     -> (t : Tree a)
          -> Positive.Dec (ALL p t)
  all f Leaf
    = Right Empty
  all f (Node v l r) with (decideE (f v))
    all f (Node v l r) | (Left x) = Left (Here x)
    all f (Node v l r) | (Right x) with (ALL.all f l)
      all f (Node v l r) | (Right x) | (Left y)
        = Left (ThereL x y)
      all f (Node v l r) | (Right x) | (Right prfL) with (ALL.all f r)
        all f (Node v l r) | (Right x) | (Right prfL) | (Left y)
          = Left (ThereR x y)
        all f (Node v l r) | (Right x) | (Right prfL) | (Right prfR)
          = Right (Branch x prfL prfR)

namespace ANY

  0
  prf : {t : Tree a} -> Any p Positive Negative t
                     -> All p Negative Positive t
                     -> Void
  prf {p = p} {t = (Node v left right)} (Here x) (Branch y prfL prfR) with (p v)
    prf {p = p} {t = (Node v left right)} (Here x) (Branch y prfL prfR) | (D positive negative cancelled)
      = cancelled x y
  prf {p = p} {t = (Node v left right)} (ThereL x ltr) (Branch y prfL prfR)
    = ANY.prf ltr prfL
  prf {p = p} {t = (Node v left right)} (ThereR x ltr) (Branch y prfL prfR)
    = ANY.prf ltr prfR

  public export
  ANY : (p : type -> Decidable) -> (t : Tree a) -> Decidable
  ANY p t = D (Any p Positive Negative t)
              (All p Negative Positive t)
              prf

  export
  any : (f : (x : a) -> Positive.Dec (p x))
     -> (t : Tree a)
          -> Positive.Dec (ANY p t)
  any f Leaf
    = Left Empty
  any f (Node v l r) with (decideE $ f v)
    any f (Node v l r) | (Left noH) with (ANY.any f l)
      any f (Node v l r) | (Left noH) | (Left noL) with (ANY.any f r)
        any f (Node v l r) | (Left noH) | (Left noL) | (Left noR)
          = Left (Branch noH noL noR)
        any f (Node v l r) | (Left noH) | (Left noL) | (Right x)
          = Right (ThereR noH x)
      any f (Node v l r) | (Left noH) | (Right x)
        = Right (ThereL noH x)
    any f (Node v l r) | (Right x)
      = Right (Here x)
