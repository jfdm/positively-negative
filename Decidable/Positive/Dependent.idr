module Decidable.Positive.Dependent

import Decidable.Positive

%default total

namespace Positive
    public export
    record DDecidable where
      constructor D
      witness : Type
      Positive : witness -> Type
      Negative : witness -> Type
      0 Cancelled : (x : witness) -> Positive x -> Negative x -> Void

    public export
    DDec : DDecidable -> Type
    DDec (D witness positive negative _)
       = Either (DPair witness negative)
                (DPair witness positive)


-- [ EOF ]
