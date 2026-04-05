import Mathlib

variable (R S M A : Type*)

variable [Semiring A]

variable [CommSemiring S] [Algebra S A] [CommSemiring R] [Algebra R S]

theorem RestrictScalars.ringEquiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) =
      algebraMap R S r • RestrictScalars.ringEquiv R S A x := rfl

