import Mathlib

variable (R S M A : Type*)

variable [AddCommMonoid M]

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.smul_def (c : R) (x : RestrictScalars R S M) :
    c • x = (RestrictScalars.addEquiv R S M).symm
      (algebraMap R S c • RestrictScalars.addEquiv R S M x) := rfl

