import public Data.So

import Decidable.Positive

import public Decidable.Positive.Bool
import        Decidable.Positive.Equality


public export
data PrimOp : (pol  : Decidable -> Type)
           -> (type : Type)
           -> (op   : type -> Bool)
           -> (p    : type)
                   -> Type
  where
    R : (prf : pol (SO (op p)))
               -> PrimOp pol t op p

public export
PRIMOP : {type : Type}
      -> (op : type -> Bool)
      -> (s  : type)
            -> Decidable
PRIMOP op s
    = D (PrimOp Positive type op s)
        (PrimOp Negative type op s) isVoid
  where
    0
    isVoid : PrimOp Positive type op p
          -> PrimOp Negative type op p
          -> Void
    isVoid (R prf) (R x)
      = (Cancels (SO $ op p)) prf x

export
primOp : (op : type -> Bool)
      -> (s  : type)
            -> Dec (PRIMOP op s)
primOp op s
  = either (Left . R)
           (Right . R)
           (isTrue (op s))

namespace Binary
  ||| Encapslates both positive and negative decisions about
  ||| boolean binary operators.
  |||
  ||| @pol is the expected polarity of the outcome.
  |||      We require this to reduce the number of
  |||      datatypes we require.
  |||
  ||| @type the type of builtins, we require this later
  |||       when hooking into predefined interfaces
  public export
  data PrimBinOp : (pol  : Decidable -> Type)
                -> (type : Type)
                -> (op   : (x,y : type) -> Bool)
                -> (x,y  : type)
                       -> Type
    where
      BinOpRes : (prf : pol (SO (op x y))) -> PrimBinOp pol type op x y
