||| Items in a Typing context.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Context.Item

import public Data.Singleton

import Decidable.Positive

public export
data Item : type -> Type where
  I : String -> Singleton ty -> Item ty


public export
data HasKey : (p : String -> Decidable)
           -> (item : Item ty)
           -> Type
  where
    HK : {0 value : Singleton v}
      -> (prfK : Positive (pK key))
              -> HasKey pK (I key value)

0
isVoidHK : HasKey         p  i
        -> HasKey (Swap . p) i
        -> Void
isVoidHK {p = p} {i = I k v} (HK po) (HK ne)
  = (p k).Cancels po ne

public export
HASKEY : (p    : String -> Decidable)
      -> (item : Item ty)
      -> Decidable
HASKEY p i
  = D (HasKey         p  i)
      (HasKey (Swap . p) i)
      isVoidHK

export
hasKey : (f : (k : String) -> Positive.Dec (p k))
      -> (item : Item ty)
              -> Positive.Dec (HASKEY p item)
hasKey f (I str x)
  = either (Left  . HK)
           (Right . HK)
           (f str)

public export
data Holds : {ty : kind}
          -> (pK   : (type : String) -> Decidable)
          -> (pI   : (type : kind)   -> Decidable)
          -> (item : Item ty)
                  -> Type
  where
    H : (prfK : Positive (pK key))
     -> (prfV : Positive (pV value))
             -> Holds pK pV (I key (Val value))

public export
data HoldsNot : {ty : kind}
             -> (pK   : (type : String) -> Decidable)
             -> (pI   : (type : kind)   -> Decidable)
             -> (item : Item ty)
                     -> Type
  where
    WrongKey : (prfKey : Positive (pK key))
                     -> HoldsNot pK pV (I key (Val value))

    WrongItem : {value : ty}
             -> (prfValue : Positive (pV value))
                         -> HoldsNot pK pV (I key (Val value))

0
isVoidU : Holds    pK                  pI item
       -> HoldsNot (Swap . pK) (Swap . pI) item
       -> Void
isVoidU {pK = pK} {item = (I key (Val value))} (H prfK prfV) (WrongKey prfKey)
  = (pK key).Cancels prfK prfKey
isVoidU {pI = pI} {item = (I key (Val value))} (H prfK prfV) (WrongItem prfValue)
  = (pI value).Cancels prfV prfValue

public export
HOLDS : (pK : (type : String) -> Decidable)
     -> (pI : (type : kind)   -> Decidable)
     -> {ty : kind}
     -> (item : Item ty)
     -> Decidable
HOLDS p k i
  = D (Holds            p          k  i)
      (HoldsNot (Swap . p) (Swap . k) i)
      isVoidU

export
holds : (f : (x : String) -> Positive.Dec (p x))
     -> (g : (x : typeS) -> Positive.Dec (q x))
     -> (x : Item type)
          -> Positive.Dec (HOLDS p q x)
holds f g (I k (Val v))
  = do pK <- f k `otherwise` WrongKey
       pI <- g v `otherwise` WrongItem
       pure (H pK pI)

-- [ EOF ]
