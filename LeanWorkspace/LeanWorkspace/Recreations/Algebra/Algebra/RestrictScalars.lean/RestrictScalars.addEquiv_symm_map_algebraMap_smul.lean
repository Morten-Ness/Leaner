import Mathlib

variable (R S M A : Type*)

variable [AddCommMonoid M]

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.addEquiv_symm_map_algebraMap_smul (r : R) (x : M) :
    (RestrictScalars.addEquiv R S M).symm (algebraMap R S r • x) =
      r • (RestrictScalars.addEquiv R S M).symm x := rfl

