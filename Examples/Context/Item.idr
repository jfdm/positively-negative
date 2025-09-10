module Examples.Context.Item

import Data.Singleton

import Data.List.Quantifiers

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.String
import Decidable.Positive.Nat
import Decidable.Positive.Pair
import Decidable.Positive.List.Assoc
import Decidable.Positive.List.Elem
import Decidable.Positive.List

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
  = (p k).Cancelled po ne

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
          -> (t    : Decidable -> Type)
          -> (item : Item ty)
                  -> Type
  where
    H : (prfK : t (pK key))
     -> (prfV : t (pV value))
             -> Holds pK pV t (I key (Val value))

public export
data HoldsNot : {ty : kind}
             -> (pK   : (type : String) -> Decidable)
             -> (pI   : (type : kind)   -> Decidable)
             -> (t    : Decidable -> Type)
             -> (item : Item ty)
                     -> Type
  where
    WrongKey :(prfKey : t (pK key))
                     -> HoldsNot pK pV t (I key (Val value))

    WrongItem : {value : ty}
             -> (prfValue : t (pV value))
                         -> HoldsNot pK pV t (I key (Val value))

0
isVoidU : Holds    pK pI Positive item
       -> HoldsNot pK pI Negative item
       -> Void
isVoidU {pK = pK} {item = (I key (Val value))} (H prfK prfV) (WrongKey prfKey)
  = (pK key).Cancelled prfK prfKey
isVoidU {pI = pI} {item = (I key (Val value))} (H prfK prfV) (WrongItem prfValue)
  = (pI value).Cancelled prfV prfValue

public export
HOLDS : (pK : (type : String) -> Decidable)
     -> (pI : (type : kind)   -> Decidable)
     -> {ty : kind}
     -> (item : Item ty)
     -> Decidable
HOLDS p k i
  = D (Holds    p k Positive i)
      (HoldsNot p k Negative i)
      isVoidU

export
holds : (f : (x : String) -> Positive.Dec (p x))
     -> (g : (x : typeS) -> Positive.Dec (q x))
     -> (x : Item type)
          -> Positive.Dec (HOLDS p q x)
holds f g (I k (Val v))
  = either (Left . WrongKey)
           (\pH => either (Left  . WrongItem)
                          (Right . H pH)
                          (g v))
           (f k)

-- [ EOF ]
