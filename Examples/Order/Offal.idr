||| Order is good.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Examples.Order.Offal

import Data.Nat

import Decidable.Positive
import Decidable.Positive.Equality
import Decidable.Positive.Order
import Decidable.Positive.Pair



import Examples.Order.Nat
import Examples.Order.SQA

public export
OLevel : Type
OLevel = Pair Nat SQA.Level


-- [ EOF ]
