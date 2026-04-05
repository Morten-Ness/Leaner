import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_symm_apply (F : R[M] →ₐ[R] A) (x : Multiplicative M) :
    (AddMonoidAlgebra.lift R A M).symm F x = F (single x.toAdd 1) := rfl

