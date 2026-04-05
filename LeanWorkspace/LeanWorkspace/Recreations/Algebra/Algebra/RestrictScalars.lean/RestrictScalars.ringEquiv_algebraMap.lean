import Mathlib

variable (R S M A : Type*)

variable [Semiring A]

variable [CommSemiring S] [Algebra S A] [CommSemiring R] [Algebra R S]

theorem RestrictScalars.ringEquiv_algebraMap (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) =
      algebraMap S A (algebraMap R S r) := rfl

