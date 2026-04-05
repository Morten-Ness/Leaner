import Mathlib

variable (R S M A : Type*)

variable [AddCommMonoid M]

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.addEquiv_map_smul (c : R) (x : RestrictScalars R S M) :
    RestrictScalars.addEquiv R S M (c • x) = algebraMap R S c • RestrictScalars.addEquiv R S M x := rfl

