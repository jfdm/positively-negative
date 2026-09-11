||| Decisions on a Typing context.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Context

import public Data.List.Quantifiers
import public Data.List.AtIndex

import public Decidable.Positive
import public Decidable.Positive.Dependent
import public Decidable.Positive.Equality
import public Decidable.Positive.Builtin
import public Decidable.Positive.Builtin.Equality
import public Decidable.Positive.List.Quantifier

import public Decidable.Positive.All.AnyAt
import public Decidable.Positive.All.Any

import public Examples.Context.Item


public export
Context : (kind : Type) -> (types : List kind) -> Type
Context _ = All Item

public export
ISBOUND : (str : String)
       -> (ctxt : Context kind xs)
       -> Decidable
ISBOUND str ctxt
  = ANY Item (HASKEY (EQUAL str)) ctxt

export
isBound : (str : String)
       -> (ctxt : Context kind xs)
               -> Positive.Dec (ISBOUND str ctxt)
isBound str ctxt
  = any (hasKey (decEq str)) ctxt


export
loc : {xs : _}
   -> {ctxt : Context kind xs}
   -> Positive (ANY     Item (HASKEY (EQUAL str)) ctxt)
   -> DPair Nat (\n => Positive (HOLDSAT      (HASKEY (EQUAL str)) ctxt  n))
loc (Here prf) = (0 ** Here prf)
loc (There prf tail) with (loc tail)
  loc (There prf tail) | ((fst ** snd)) = (S fst ** There snd)

export
deBruijn : {xs : _}
        -> {ctxt : All Item xs}
        -> Positive (HOLDSAT (HASKEY (EQUAL key)) ctxt n)
        -> DPair kind (\t => AtIndex t xs n)
deBruijn (Here {x=I k (Val v)} (HK prfK))
  = (v ** Z)
deBruijn (There tail) with (deBruijn tail)
  deBruijn (There tail) | (fst ** snd) = (fst ** S snd)

namespace Experimental
  public export
  ISBOUNDAT : (str : String)
           -> (ctxt : Context kind xs)
           -> DDecidable
  ISBOUNDAT str ctxt
    = HOLDSAT (HASKEY (EQUAL str)) ctxt

  export
  isBound : {xs : List kind}
         -> (str  : String)
         -> (ctxt : Context kind xs)
                 -> DDec (ISBOUNDAT str ctxt)
  isBound str ctxt
    = holdsAt (hasKey (decEq str)) ctxt


  namespace Context
    public export
    HOLDSFOR : (str : String)
           -> (p : (x : kind) -> Decidable)
           -> (ctxt : Context kind xs)
                 -> DDecidable
    HOLDSFOR str p ctxt
      = HOLDSAT (HOLDS (EQUAL str) p) ctxt

    export
    holdsFor : {0 p : (x : kind) -> Decidable}
            -> (f : (x : kind) -> Positive.Dec (p x))
            -> (str : String)
            -> (xs : Context kind is)
                 -> Positive.DDec (HOLDSFOR str p xs)
    holdsFor f str []
      = Left (Z ** Empty)
    holdsFor f x (I y i :: rest) with (decEq x y)
      holdsFor f x (I y i :: rest) | (Left z) with (holdsFor f x rest)
        holdsFor f x (I y i :: rest) | (Left z) | (Left (fst ** snd))
          = Left (S fst ** T snd)
        holdsFor f x (I y i :: rest) | (Left z) | (Right (fst ** snd))
          = Right (S fst ** There snd)

      holdsFor f x (I y (Val i) :: rest) | (Right pH) with (f i)
        holdsFor f x (I y (Val i) :: rest) | (Right pH) | (Left pN)
          = Left (0 ** H (WrongItem pN))
        holdsFor f x (I y (Val i) :: rest) | (Right pH) | (Right pV)
          = Right (0 ** Here (H pH pV))


-- [ EOF ]
