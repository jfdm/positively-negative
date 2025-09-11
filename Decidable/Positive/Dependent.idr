||| Decidable decisions on Association lists.
|||
||| Copyright : see COPYRIGHT
||| License   : see LICENSE
|||
module Decidable.Positive.Dependent

%default total

namespace Dependent
  namespace Positive
    public export
    record DDecidable where
      constructor D
      witness : Type
      Positive : witness -> Type
      Negative : witness -> Type
      0 Cancels : (x : witness) -> Positive x -> Negative x -> Void

    public export
    DDec : DDecidable -> Type
    DDec d
       = Either (DPair (witness d) (Negative d))
                (DPair (witness d) (Positive d))

    public export
    NEGATIVE : DDecidable -> Type
    NEGATIVE d
      = DPair (witness d) (Negative d)

    POSITIVE : DDecidable -> Type
    POSITIVE d
      = DPair (witness d) (Positive d)


-- [ EOF ]
