module Examples

import Decidable.Positive
import Decidable.Positive.Nat
import Decidable.Positive.List.Elem
import Decidable.Positive.List.All

%default total

namespace Main

  export
  main : IO ()
  main
    = do putStrLn (show (GreaterThan.isGT 3 1))
         putStrLn (show (GreaterThan.isGT 1 3))

         putStrLn (showALL {p = GT 3}
                           (\x => "Yes " <+> show x)
                           (\x => "No " <+> show x)
                           (All.all (GreaterThan.isGT 3) [1,2,3]))

         putStrLn (showALL {p = GT 3}
                           (\x => "Yes " <+> show x)
                           (\x => "No " <+> show x)
                           (All.all (GreaterThan.isGT 3) [4,5,6]))

         putStrLn (showALL {p = GT 3}
                           (\x => "Yes " <+> show x)
                           (\x => "No " <+> show x)
                           (All.all (GreaterThan.isGT 3) [1,0,1]))
-- [ EOF ]
