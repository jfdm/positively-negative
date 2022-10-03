module Decidable.Positive.List.All

import public Decidable.Positive

%default total

public export
data All : (pred : (value : type)
                -> Decidable)
        -> (xs   : List type)
                -> Type
  where
    Empty : All p Nil
    Extend : {x    : type}
          -> {0 p  : type -> Decidable}
          -> (prf  : Pos (p x))
          -> (rest : All p     xs)
                  -> All p (x::xs)

export
showAll : (f : forall x . Pos (p x) -> String)
       -> All p xs
       -> String
showAll f Empty = "[]"
showAll f (Extend prf rest)
  = "\{f prf} :: \{showAll f rest}"


public export
data Any : (pred : (value : type)
                -> Decidable)
           -> (xs : List type)
                 -> Type
  where
    Here : (prf : Neg (p x))
               -> Any p (x::xs)

    There : {x : type}
         -> {0 p : type -> Decidable}
         -> (prf  : Pos (p x))
         -> (rest : Any p     xs)
                 -> Any p (x::xs)

export
showAny : (f : forall x . Positive.Pos (p x) -> String)
       -> (g : forall x . Positive.Neg (p x) -> String)
       -> Any p xs
       -> String
showAny f g (Here prf) = g prf
showAny f g (There prf rest)
  = "\{f prf} :: \{showAny f g rest}"


public export
0
prf : {xs  : List type}
   -> All p xs
   -> Any p xs
   -> Void
prf Empty (Here neg) impossible
prf Empty (There pos rest) impossible

prf {p} {xs=(x::xs)} (Extend pos rest) (Here neg) with (p x)
  prf {p = p} {xs=(x::xs)} (Extend pos rest) (Here neg) | (D _ _ no)
    = no pos neg

prf {p} {xs=(x::xs)} (Extend pos rest) (There pos' later) with (All.prf rest later)
  prf {p} {xs=(x::xs)} (Extend pos rest) (There pos' later) | boom = boom


public export
ALL : (p : type -> Decidable) -> (xs : List type) -> Decidable
ALL p xs
  = D (All     p xs)
      (Any     p xs)
      (All.prf)

export
all : {p : type -> Decidable}
   -> (f  : (x : type) -> Positive.Dec (p x))
   -> (xs : List type)
         -> Positive.Dec (ALL p xs)
all f []
  = Right Empty

all {p} f (x :: xs) with (p x)
  all {p = p} f (x :: xs) | (D y n prf) with (f x)
    all {p = p} f (x :: xs) | (D y n prf) | res with (polarity' res)
      all {p = p} f (x :: xs) | (D y n prf) | res | (Left r)
        = Left (Here r)

      all {p = p} f (x :: xs) | (D y n prf) | res | (Right r) with (All.all f xs)
        all {p = p} f (x :: xs) | (D y n prf) | res | (Right r) | (Left rs)
          = Left (There r rs)
        all {p = p} f (x :: xs) | (D y n prf) | res | (Right r) | (Right rs)
          = Right (Extend r rs)

export
showALL : (f : forall x . Pos (p x) -> String)
       -> (g : forall x . Neg (p x) -> String)
       -> Positive.Dec (ALL p xs)
       -> String
showALL f g (Left x)
  = "No \{showAny f g x}"
showALL f g (Right x)
  = "Yes \{showAll f x}"

-- [ EOF ]
