module Decidable.Positive.Dependent

import Decidable.Positive

%default total

namespace Dependent
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
    DDec d
       = Either (DPair (witness d) (Negative d))
                (DPair (witness d) (Positive d))


-- [ EOF ]
