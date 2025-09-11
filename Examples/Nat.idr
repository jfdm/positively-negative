||| Examples on Nats and Lists
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Nat
import Decidable.Positive.List
import Decidable.Positive.List.Elem
import Decidable.Positive.List.Quantifier

%default total


namespace Main

  export
  main : IO ()
  main
    = do putStrLn "# GT"
         putStrLn "## Is 3 > 1"
         putStrLn (either (show @{Helper}) (show @{Helper}) (Positive.Nat.isGT 3 1))
         putStrLn "## Is 1 > 3"
         putStrLn (either (show @{Helper}) (show @{Helper}) (Positive.Nat.isGT 1 3))

         putStrLn "# All"
         putStrLn "## forall x \in [1,2,3], 3 > x"

         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (all (isGT 3) [1,2,3]))

         putStrLn "## forall x \in [4,5,6], 3 > x"
         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (all (isGT 3) [4,5,6]))

         putStrLn "## forall x \in [1,0,1], 3 > x"
         putStrLn (showALL {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (all (isGT 3) [1,0,1]))

         putStrLn "# Any"
         putStrLn "## exists an x \in [1,2,3], 3 > x\n"
         putStrLn (showANY {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (any (isGT 3) [1,2,3]))

         putStrLn "## exists an x \in [4,5,6], 3 > x"
         putStrLn (showANY {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (any (isGT 3) [4,5,6]))

         putStrLn "## exists an x \in [1,0,1], 3 > x"
         putStrLn (showANY {p = GT 3}
                           (\x => "(Yes \{show @{Helper} x})")
                           (\x => "(No \{show @{Helper} x})")
                           (any (isGT 3) [1,0,1]))


-- [ EOF ]
