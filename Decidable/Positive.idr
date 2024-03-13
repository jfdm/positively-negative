module Decidable.Positive

%default total

public export
record Decidable where
  constructor D
  Positive : Type
  Negative : Type
  0 Cancelled : Positive -> Negative -> Void

public export
Show : Decidable -> Type
Show (D p n _) = (Show p, Show n)

export
negSym : (no  : p -> n -> Void)
            -> (n -> p -> Void)
negSym no x y = no y x


||| This function is entirely Bob's idea.
public export
0
Dec : Decidable -> Type
Dec (D p q no)
  = Either q p

public export
data Polarity : (d : Decidable) -> Positive.Dec d -> Type where
  IN : Polarity (D p q no) (Left val)
  IP : Polarity (D p q no) (Right val)

export
polarity : {d : Decidable} -> (r : Positive.Dec d) -> Polarity d r
polarity {d = (D p n no)} (Left _) = IN
polarity {d = (D p n no)} (Right _) = IP

show : {d : Decidable}
    -> Show d
    => (prf : Positive.Dec d)
           -> String
show prf with (polarity prf)
  show (Left val) | IN
    = show val
  show (Right val) | IP
    = show val

export
{d : Decidable} -> Show d => Show (Positive.Dec d) where
  show x = Positive.show x

export
polarity' : {d   : Decidable}
         -> (res : Positive.Dec d)
                -> Either (Negative d) (Positive d)
polarity' {d = (D positive negative cancelled)} (Left x)
  = Left x
polarity' {d = (D positive negative cancelled)} (Right x)
  = Right x

||| Propositional equality is builtin, and sadly equality cannot be truely positve.
namespace Equality

  prf : Equal x y -> Not (Equal x y) -> Void
  prf Refl no
    = no Refl

  public export
  EQ : (x,y : type) -> Decidable
  EQ x y
    = D (Equal x y)
        (Not (Equal x y))
        prf

  public export
  interface DecEq type where
    decEq : (x,y : type)
                -> Positive.Dec (EQ x y)

  namespace Positive
    public export
    interface DecEqPos type where
      DECEQpos : (x,y : type) -> Type
      DECEQneg : (x,y : type) -> Type
      0 DECEQprf : forall x, y . DECEQpos x y -> DECEQneg x y -> Void

      DECEQ : (x,y : type) -> Decidable
      DECEQ x y = D (DECEQpos x y) (DECEQneg x y) DECEQprf

      DECEQIN : (x,y : type) -> Decidable
      DECEQIN x y = D (DECEQneg x y) (DECEQpos x y) (\x,y => DECEQprf y x)

      0 DECEQeq : forall x, y . DECEQpos x y -> Equal x y
      0 DECEQeqn : forall x, y . DECEQpos x y -> DECEQneg x y -> Not (Equal x y)

      decEqPOS : (x,y : type)
                     -> Positive.Dec (DECEQ x y)

      decEqPOSNot : (x,y : type)
                        -> Positive.Dec (DECEQIN x y)

-- [ EOF ]
