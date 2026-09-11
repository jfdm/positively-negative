||| Decidable things for Srings go here.
|||
||| When usingi `SO`/`OH` directly, the decisions will not
||| be informative. Here we give an example of a bespoke
||| String predicate (has length) to show how to be more
||| informative when making decisions about primitives.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.String

import Decidable.Positive
import public Decidable.Positive.Bool
import public Decidable.Positive.Equality
import public Decidable.Positive.Builtin

%default total

||| A synonym to make writing specifications easier.
public export
hasLengthN : (n : Nat) -> (s : String) -> Bool
hasLengthN n s
  = length s == n

|||
public export
data HasLength : (b   : Decidable -> Type)
              -> (s   : String)
              -> (n   : Nat)
                     -> Type where
  HL : (  s   : String)
    -> (  n   : Nat)
    -> (  prf : pol (SO (hasLengthN n s)))
             -> HasLength pol s n

public export
HASLENGTH : (s : String)
         -> (n : Nat)
              -> Decidable
HASLENGTH s n
  = D (HasLength Positive s n)
      (HasLength Negative s n)
      prf
  where
  0
  prf : forall s, n
      . HasLength Positive  s n
     -> HasLength Negative  s n
     -> Void
  prf (HL s n x) (HL s n y)
    = (Cancels (SO $ hasLengthN n s)) x y

public export
HASLENGTHNOT : (s : String) -> (n : Nat) -> Decidable
HASLENGTHNOT s n = Swap (HASLENGTH s n)

export
hasLength : (s : String)
         -> (n : Nat)
              -> Dec (HASLENGTH s n)
hasLength s n
  = either (Left  . HL s n)
           (Right . HL s n)
           (primOpUnSo (hasLengthN n) s)

export
hasLengthNot : (s : String) -> (n : Nat) -> Dec (HASLENGTHNOT s n)
hasLengthNot s n = mirror $ hasLength s n

-- [ EOF ]
