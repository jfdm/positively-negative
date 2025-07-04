module Examples

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Nat
import Decidable.Positive.List
import Decidable.Positive.List.Elem
import Decidable.Positive.List.Quantifier
import Decidable.Positive.List.Quantifier.Any.Wrong

%default total


namespace Main

  export
  main : IO ()
  main
    = do putStrLn "# GT"
         putStrLn "## Is 3 > 1"
         putStrLn (show (GreaterThan.isGT 3 1))
         putStrLn "## Is 1 > 3"
         putStrLn (show (GreaterThan.isGT 1 3))

         putStrLn "# All"
         putStrLn "## forall x \in [1,2,3], 3 > x"

         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (all (GreaterThan.isGT 3) [1,2,3]))

         putStrLn "## forall x \in [4,5,6], 3 > x"
         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (all (GreaterThan.isGT 3) [4,5,6]))

         putStrLn "## forall x \in [1,0,1], 3 > x"
         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (all (GreaterThan.isGT 3) [1,0,1]))

         putStrLn "# Any (Wrong)"
         putStrLn "## (Wrong) exists an x \in [1,2,3], 3 > x\n"
         putStrLn (Wrong.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (Any.Wrong.any (GreaterThan.isGT 3) [1,2,3]))

         putStrLn "## (Wrong) exists an x \in [4,5,6], 3 > x"
         putStrLn (Wrong.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (Any.Wrong.any (GreaterThan.isGT 3) [4,5,6]))

         putStrLn "## (Wrong) exists an x \in [1,0,1], 3 > x"
         putStrLn (Wrong.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (Any.Wrong.any (GreaterThan.isGT 3) [1,0,1]))

         putStrLn "# Any"
         putStrLn "## exists an x \in [1,2,3], 3 > x\n"
         putStrLn (Any.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (any (GreaterThan.isGT 3) [1,2,3]))

         putStrLn "## exists an x \in [4,5,6], 3 > x"
         putStrLn (Any.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (any (GreaterThan.isGT 3) [4,5,6]))

         putStrLn "## exists an x \in [1,0,1], 3 > x"
         putStrLn (Any.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (any (GreaterThan.isGT 3) [1,0,1]))



         putStrLn "## W"
         putStrLn (Wrong.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (Any.Wrong.any (GreaterThan.isGT 3) [1,2,3]))

         putStrLn "## C"
         putStrLn (Any.showANY {p = GT 3}
                           (\x => "(Yes \{show x})")
                           (\x => "(No \{show x})")
                           (any (GreaterThan.isGT 3) [1,2,3]))

-- [ EOF ]
