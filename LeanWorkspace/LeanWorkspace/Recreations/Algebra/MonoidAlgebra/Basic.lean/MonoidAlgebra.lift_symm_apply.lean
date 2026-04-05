import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_symm_apply (F : R[M] →ₐ[R] A) (m : M) : (MonoidAlgebra.lift R A M).symm F m = F (single m 1) := rfl

