module Examples.Context

import Data.Singleton

import public Data.List.Elem

import public Data.List.Quantifiers

import public Decidable.Positive
import public Decidable.Positive.Equality
import public Decidable.Positive.So
import public Decidable.Positive.String
import public Decidable.Positive.Nat
import public Decidable.Positive.Pair
import public Decidable.Positive.List.Assoc
import public Decidable.Positive.List.Elem
import public Decidable.Positive.List.Quantifier.All
import public Decidable.Positive.List.Quantifier.Any

import public Decidable.Positive.All.Any
import public Decidable.Positive.All.AnyAt
import public Decidable.Positive.List.ElemAt

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
loc :                  Positive (ANY     Item (HASKEY (EQUAL str)) ctxt)
   -> DPair Nat (\n => Positive (HOLDSAT      (HASKEY (EQUAL str)) ctxt  n))
loc (Here prf) = (0 ** Here prf)
loc (There prf tail) with (loc tail)
  loc (There prf tail) | ((fst ** snd)) = (S fst ** There snd)

public export
data AtIndex : (x   :      type)
            -> (xs  : List type)
            -> (idx : Nat)
                   -> Type
  where
    Here : AtIndex x (x::xs) Z
    There : (later : AtIndex x     rest     idx)
                  -> AtIndex x (y::rest) (S idx)

export
deBruijn : {ctxt : All Item xs}
        -> Positive (HOLDSAT (HASKEY (EQUAL key)) ctxt n)
        -> DPair kind (\t => AtIndex t xs n)
deBruijn (Here {x=I k (Val v)} (HK prfK))
  = (v ** Here)
deBruijn (There tail) with (deBruijn tail)
  deBruijn (There tail) | (fst ** snd) = (fst ** There snd)


-- [ EOF ]
