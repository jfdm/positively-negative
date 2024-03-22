module Examples.Context

import Data.Singleton

import public Data.List.Elem
import Data.List.Quantifiers

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

import public Examples.Context.Item


public export
Context : (kind : Type) -> (types : List kind) -> Type
Context _ = All Item

public export
data Exists : (kind : Type)
           -> (pK   : (key  : String) -> Decidable)
           -> (pV   : (type : kind) -> Decidable)
           -> {xs   : List kind}
           -> (ctxt : Context kind xs)
                   -> Type
  where
   E : (value : kind)
    -> (prfI  : Positive (pv value))
    -> (prfV  : Positive (ANY Item (HOLDS pk pv) ctxt))
    -> Exists kind pk pv ctxt


public export
data ExistsNot : (kind : Type)
              -> (pK   : (key  : String) -> Decidable)
              -> (pV   : (type : kind) -> Decidable)
              -> {xs   : List kind}
              -> (ctxt : Context kind xs)
                      -> Type
  where
   NotFound : Negative (ANY Item (HOLDS pK pV) ctxt)
           -> ExistsNot kind pK pV ctxt

0
isVoid : Exists    kind pK pV ctxt
      -> ExistsNot kind pK pV ctxt
      -> Void
isVoid {pK} {pV} (E value prfI prfV) (NotFound x)
  = All.Any.isVoid prfV x


public export
EXISTS : {kind : Type}
      -> {xs   : List kind}
      -> (pK    : String -> Decidable)
      -> (pV    : kind -> Decidable)
      -> (ctxt : Context kind xs)
      -> Decidable
EXISTS pK pV ctxt
  = D (Exists    kind pK pV ctxt)
      (ExistsNot kind pK pV ctxt)
      isVoid

export
exists : Positive.DecEq String
      => {xs   : _}
      -> (f    : (type : kind) -> Positive.Dec (p type))
      -> (key  : String)
      -> (ctxt : Context kind xs)
              -> Positive.Dec (EXISTS (DECEQ key) p ctxt)
exists f key []
  = Left (NotFound Empty)

exists f key (kv :: kvs) with (holds (decEq key) f kv)
  exists f key (kv :: kvs) | (Left x) with (exists f key kvs)
    exists f key ((I key' (Val x)) :: kvs) | (Left why) | (Left (NotFound y))
      = Left (NotFound $ Extend why y)
    exists f key (kv :: kvs) | (Left x) | (Right (E value prfI prfV))
      = Right (E value prfI (There x prfV))

  exists f key ((I key' (Val x)) :: kvs) | (Right (H prfK prfV))
    = Right (E x prfV (Here (H prfK prfV)))


-- [ EOF ]
