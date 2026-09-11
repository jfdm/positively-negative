||| Decidable equality for builtins.
|||
||| The decisions here are not informative and mirrors how
||| it is down in Idris for such things.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Builtin

import public Data.So

import Decidable.Positive

import public Decidable.Positive.Bool
import        Decidable.Positive.Equality

%default total


||| Uninformative, yet decidable, decision for whether
||| the given unary boolean operation `op` hold for `s`.
|||
||| @op the unary operation being performed on values,
|||     we expect positive decisions to be true and
|||     negative ones to true.
||| @s  the value being reasoned about.
|||
export
primOpUnSo : (op : type -> Bool)
        -> (s  : type)
              -> Dec (SO (op s))
primOpUnSo op s
  = isTrue (op s)

||| Uninformative, yet decidable, decision for whether
||| the given unary boolean operation `op` does not hold
||| for `s`.
|||
||| @op the unary operation being performed on values,
|||     we expect positive decisions to be true and
|||     negative ones to true.
||| @s  the value being reasoned about.
|||
export
primOpUnOh : (op : type -> Bool)
        -> (s  : type)
              -> Dec (OH (op s))
primOpUnOh op s
  = isFalse (op s)

||| Uninformative, yet decidable, decision for whether
||| the given binary boolean operation `op` holds for
||| `x` and `y`.
|||
||| @op the unary operation being performed on values,
|||     we expect positive decisions to be true and
|||     negative ones to true.
||| @s  the value being reasoned about.
|||
export
primOpBinSo : (op  : (x,y : type) -> Bool)
           -> (x,y : type)
                  -> Dec (SO (op x y))
primOpBinSo op x y
  = isTrue (op x y)

||| Uninformative, yet decidable, decision for whether
||| the given binary boolean operation `op` does not hold
|||  for `x` and `y`.
|||
||| @op the unary operation being performed on values,
|||     we expect positive decisions to be true and
|||     negative ones to true.
||| @s  the value being reasoned about.
|||
export
primOpBinOh : (op  : (x,y : type) -> Bool)
           -> (x,y : type)
                  -> Dec (OH (op x y))
primOpBinOh op x y
  = isFalse (op x y)

-- [ EOF ]
