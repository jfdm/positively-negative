module Decidable.Positive.List.Quantifier

import public Decidable.Positive

%default total

namespace List
  public export
  data All : (pred : (value : type) -> Decidable)
          -> (pos  : Decidable -> Type)
          -> (neg  : Decidable -> Type)
          -> (xs   : List type)
                  -> Type
    where
      Empty : All p pos neg Nil
      Extend : {x    : type}
            -> {0 p  : type -> Decidable}
            -> (prf  : pos (p x))
            -> (rest : All p pos neg     xs)
                    -> All p pos neg (x::xs)

  export
  showAll : (f : {x : _} -> pos (p x) -> String)
         -> All p pos neg xs
         -> String
  showAll f Empty
    = "[]"

  showAll f (Extend prf rest)
    = "(\{f prf} :: \{showAll f rest})"

  public export
  data Any : (pred : (value : type) -> Decidable)
          -> (pos  : Decidable -> Type)
          -> (neg  : Decidable -> Type)
          -> (xs   : List type)
                  -> Type
    where
      Here : {x   : type}
          -> (prf : pos (p x))
                 -> Any p pos neg (x::xs)

      There : {x : type}
           -> (prf : neg (p x))
           -> (rest : Any p pos neg     xs)
                   -> Any p pos neg (x::xs)

  export
  showAny : (f : {x : _} -> pos (p x) -> String)
         -> (g : {x : _} -> neg (p x) -> String)
         -> Any p pos neg xs
         -> String
  showAny f g (Here prf)
    = f prf
  showAny f g (There prf rest)
    = "(\{g prf} :: \{showAny f g rest})"


  namespace All

    export
    0
    prf : {xs  : List type}
       -> All p Positive Negative xs
       -> Any p Negative Positive xs
       -> Void
    prf Empty (Here x) impossible
    prf Empty (There x rest) impossible

    prf {p} {xs=(x::xs)} (Extend pos rest) any with (any)
      prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (Here neg)
        = (p x).Cancelled pos neg
      prf {p = p} {xs=(x::xs)} (Extend pos rest) any | (There pos' later)
        = All.prf rest later


    public export
    ALL : (p : type -> Decidable) -> (xs : List type) -> Decidable
    ALL p xs
      = D (All     p Positive Negative xs)
          (Any     p Negative Positive xs)
          (prf)

    export
    all : (f  : (x : type) -> Positive.Dec (p x))
       -> (xs : List type)
             -> Positive.Dec (ALL p xs)
    all f []
      = Right Empty

    all {p} f (x :: xs)
      = either (Left . Here)
               (\noH => either (Left  . There noH)
                               (Right . Extend noH)
                               (all f xs))
               (f x)

    export
    showALL : (f : {x:_} -> Positive (p x) -> String)
           -> (g : {x:_} -> Negative (p x) -> String)
           -> Positive.Dec (ALL p xs)
           -> String
    showALL f g (Left x)
      = "(No (Any) \{showAny g f x})"
    showALL f g (Right x)
      = "(Yes (All) \{showAll f x})"

  namespace Any
    0
    prf : {xs  : List type}
       -> Any p Positive Negative xs
       -> All p Negative Positive xs
       -> Void
    prf {p} {xs=x::xs} (Here neg) (Extend pos rest)
      = (p x).Cancelled neg pos

    prf {p} {xs=x::xs} (There pos rest) (Extend neg later)
      = prf rest later


    public export
    ANY : (p : type -> Decidable) -> (xs : List type) -> Decidable
    ANY p xs
      = D (Any     p Positive Negative xs)
          (All     p Negative Positive xs)
          (prf)

    export
    any : (f  : (x : type) -> Positive.Dec (p x))
       -> (xs : List type)
             -> Positive.Dec (ANY p xs)
    any f []
      = Left Empty

    any f (x :: xs)
      = either (\noH => either (Left . Extend noH)
                               (Right . There noH)
                               (any f xs))
               (Right . Here)
               (f x)

    export
    showANY : (f : {x : _} -> Positive (p x) -> String)
           -> (g : {x : _} -> Negative (p x) -> String)
           -> Positive.Dec (ANY p xs)
           -> String
    showANY f g (Left x) = "(No (All) \{showAll g x})"
    showANY f g (Right x) = "(Yes (Any) \{showAny f g x})"


-- [ EOF ]
