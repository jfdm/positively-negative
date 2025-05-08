module Examples.Elab.Razor

import Data.Singleton

import Decidable.Positive
import Decidable.Positive.String
import Decidable.Positive.Nat
import Decidable.Positive.Pair
import Decidable.Positive.List.Assoc
import Decidable.Positive.List.Elem
import Decidable.Positive.List.Quantifier.All
import Decidable.Positive.List.Quantifier.Any


%default total



public export
data AST = Var String
         | Let String AST AST
         | Nat Nat
         | Add AST AST

public export
data Razor : List String -> Type
  where
    V : {x,xs : _} -> Positive (ELEM x xs)
     -> Razor xs

    L : Razor xs
     -> Razor (x::xs)
     -> Razor xs

    N : Nat -> Razor xs
    P : (x,y : Razor xs) -> Razor xs

public export
data Error : List String -> Type where
   NotBound : (x : String) -> Negative (ELEM x xs) -> Error xs
   Eek : Error (x::xs) -> Error xs

export
elab : (xs : List String)
    -> AST
    -> Either (Error xs)
              (Razor xs)
elab xs (Var str)
  = decidable {d=ELEM str xs}
              (isElem str xs)
              (Left . NotBound str)
              (Right . V)


elab xs (Let str v b)
  = do v <- elab xs v
       case elab (str::xs) b of
         Left err => Left (Eek err)
         Right b =>
           pure (L v b)

elab xs (Nat k)
  = Right (N k)

elab xs (Add x y)
  = do x <- elab xs x
       y <- elab xs y
       pure (P x y)

showIDX : Any p pos neg xs -> String
showIDX x = Core.showAny (const "T") (const "H") x

Show (Razor ctxt) where
  show (V x)
    = showIDX x
  show (L x y)
    = "let \{show x} in \{show y}"
  show (N k) = show k
  show (P x y)
    = "(\{show x} + \{show y})"

show : {s,x : String} -> AreEqual Negative s x -> String
show {x} {s} (Same prf) = "Not Equal \{x} & \{s}"

Show (Error xs) where
  show (Eek e) = show e
  show (NotBound s prf) = "Not bound: \{s}\n\n Why:\n\n \{Core.showAll (\p => show p) prf}"

export
run : AST -> IO ()
run
  = (printLn . elab Nil)
