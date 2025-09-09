module Examples.Tree


import public Decidable.Positive
import public Decidable.Positive.Equality
import Decidable.Positive.Nat

%default total

data Tree a = Leaf | Node a (Tree a) (Tree a)

public export
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


public export
ALL : (p : type -> Decidable) -> (t : Tree type) -> Decidable
ALL p t = D (All p Positive Negative t)
            (Any p Negative Positive t)
            prf
  where
    0
    prf : {p : type -> Decidable}
       -> {t : Tree type} -> All p Positive Negative t
                          -> Any p Negative Positive t
                          -> Void
    prf Empty (Here x) impossible
    prf Empty (ThereL x ltr) impossible
    prf Empty (ThereR x ltr) impossible
    prf {p} {t=Node v l r} (Branch x prfL prfR) ant with (ant)
      prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (Here prfA)
          = (p v).Cancelled x prfA
      prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (ThereL prfA ltr)
        = prf prfL ltr
      prf {p} {t=Node v l r} (Branch x prfL prfR) ant | (ThereR prfA ltr)
        = prf prfR ltr

export
all : (f : (x : a) -> Positive.Dec (p x))
   -> (t : Tree a)
        -> Positive.Dec (ALL p t)
all f Leaf
  = Right Empty
all f (Node v l r) with ((f v))
  all f (Node v l r) | (Left x) = Left (Here x)
  all f (Node v l r) | (Right x) with (Tree.all f l)
    all f (Node v l r) | (Right x) | (Left y)
      = Left (ThereL x y)
    all f (Node v l r) | (Right x) | (Right prfL) with (Tree.all f r)
      all f (Node v l r) | (Right x) | (Right prfL) | (Left y)
        = Left (ThereR x y)
      all f (Node v l r) | (Right x) | (Right prfL) | (Right prfR)
        = Right (Branch x prfL prfR)

public export
ANY : (p : type -> Decidable) -> (t : Tree type) -> Decidable
ANY p t = D (Any p Positive Negative t)
            (All p Negative Positive t)
            prf

  where
    0
    prf : {p : type -> Decidable}
       -> {t : Tree type} -> Any p Positive Negative t
                          -> All p Negative Positive t
                         -> Void
    prf {p = p} {t = (Node v left right)} (Here x) (Branch y prfL prfR)
        = (p v).Cancelled x y
    prf {p = p} {t = (Node v left right)} (ThereL x ltr) (Branch y prfL prfR)
      = prf ltr prfL
    prf {p = p} {t = (Node v left right)} (ThereR x ltr) (Branch y prfL prfR)
      = prf ltr prfR



export
any : (f : (x : a) -> Positive.Dec (p x))
   -> (t : Tree a)
        -> Positive.Dec (ANY p t)
any f Leaf
  = Left Empty
any f (Node v l r) with (f v)
  any f (Node v l r) | (Left noH) with (Tree.any f l)
    any f (Node v l r) | (Left noH) | (Left noL) with (Tree.any f r)
      any f (Node v l r) | (Left noH) | (Left noL) | (Left noR)
        = Left (Branch noH noL noR)
      any f (Node v l r) | (Left noH) | (Left noL) | (Right x)
        = Right (ThereR noH x)
    any f (Node v l r) | (Left noH) | (Right x)
      = Right (ThereL noH x)
  any f (Node v l r) | (Right x)
    = Right (Here x)

data Shape : (l,r : Tree a) -> Type where
  BothEmpty : Shape Leaf Leaf
  HeavyL : Shape (Node v l r) Leaf
  HeavyR : Shape Leaf (Node v l r)
  BothN : (x,y : a)
       -> (prfL : Shape xl yl)
       -> (prfR : Shape xr yr)
               -> Shape (Node x xl xr)
                        (Node y yl yr)

data TreeCmp2 : (p : (x,y : type) -> Decidable)
             -> (x,y : Tree type)
                    -> Type
  where
    CmpH : TreeCmp2 p Leaf Leaf
    CmpT : {p : (x,y : type) -> Decidable}
        -> (prf : (p x y).Positive)
        -> (prfL : TreeCmp2 p xl yl)
        -> (prfR : TreeCmp2 p xr yr)
                -> TreeCmp2 p (Node x xl xr)
                              (Node y yl yr)

data TreeCmp2Not : (p : (x,y : type) -> Decidable)
               -> (x,y : Tree type)
                      -> Type
  where
    CmpHeavyL : TreeCmp2Not p (Node v l r) Leaf
    CmpHeavyR : TreeCmp2Not p Leaf (Node v l r)
    CmpNoLeft : TreeCmp2Not p xl yl
             -> TreeCmp2Not p (Node x xl xr)
                              (Node y yl yr)
    CmpNoRight : {p : (x,y : type) -> Decidable}
              -> TreeCmp2Not p xr yr
              -> TreeCmp2Not p (Node x xl xr)
                               (Node y yl yr)
    CmpNoHead : {p : (x,y : type) -> Decidable}
             -> (prf : (p x y).Negative)
              -> TreeCmp2Not p (Node x xl xr)
                               (Node y yl yr)
0
prfCan : DecEQ type
      => {x,y : Tree type}
      -> TreeCmp2    EQUAL x y
      -> TreeCmp2Not EQUAL x y
      -> Void
prfCan CmpH CmpHeavyL impossible
prfCan CmpH CmpHeavyR impossible
prfCan CmpH (CmpNoLeft z) impossible
prfCan CmpH (CmpNoRight prf z) impossible
prfCan CmpH (CmpNoHead prf z) impossible

prfCan (CmpT prf prfL prfR) (CmpNoLeft rest) = prfCan prfL rest
prfCan (CmpT prf prfL prfR) (CmpNoRight rest) = prfCan prfR rest
prfCan {x=Node x xl xr} {y=Node y yl yr} (CmpT prf prfL prfR) (CmpNoHead no)
  = (EQUAL x y).Cancelled prf no

asREFL : DecEQ a => {x,y : Tree a} -> TreeCmp2 EQUAL x y -> Equal x y
asREFL CmpH = Refl
asREFL (CmpT prf prfL prfR) with (toRefl prf)
  asREFL (CmpT prf prfL prfR) | Refl with (asREFL prfL)
    asREFL (CmpT prf prfL prfR) | Refl | Refl with (asREFL prfR)
      asREFL (CmpT prf prfL prfR) | Refl | Refl | Refl = Refl

0
asVOID : DecEQ a => {x,y : Tree a} -> TreeCmp2Not EQUAL x y -> Equal x y -> Void
asVOID CmpHeavyL Refl impossible
asVOID CmpHeavyR Refl impossible
asVOID (CmpNoLeft z) Refl = asVOID z Refl
asVOID (CmpNoRight z) Refl = asVOID z Refl
asVOID {x=Node x xl xr} {y=Node x xl xr} (CmpNoHead z) Refl = toVoid z Refl


DecEQ a => DecEQ (Tree a) where
  EQUAL x y = D (TreeCmp2    EQUAL x y)
                (TreeCmp2Not EQUAL x y)
                prfCan

  toRefl = asREFL
  toVoid = asVOID

  decEq Leaf Leaf
    = Right CmpH
  decEq Leaf (Node x y z)
    = Left CmpHeavyR
  decEq (Node x z w) Leaf
    = Left CmpHeavyL
  decEq (Node x xl xr) (Node y yl yr) with (decEq x y)
    decEq (Node x xl xr) (Node y yl yr) | (Left prfH)
      = Left (CmpNoHead prfH)
    decEq (Node x xl xr) (Node y yl yr) | (Right prfH) with (decEq xl yl)
      decEq (Node x xl xr) (Node y yl yr) | (Right prfH) | (Left prfL)
        = Left (CmpNoLeft prfL)
      decEq (Node x xl xr) (Node y yl yr) | (Right prfH) | (Right prfL) with (decEq xr yr)
        decEq (Node x xl xr) (Node y yl yr) | (Right prfH) | (Right prfL) | (Left prfR)
          = Left (CmpNoRight prfR)
        decEq (Node x xl xr) (Node y yl yr) | (Right prfH) | (Right prfL) | (Right prfR)
          = Right (CmpT prfH prfL prfR)

  refl Leaf
    = CmpH
  refl (Node x y z)
    = CmpT (refl x) (refl y) (refl z)
