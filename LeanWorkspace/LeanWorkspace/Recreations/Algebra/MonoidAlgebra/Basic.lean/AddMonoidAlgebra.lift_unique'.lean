import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_unique' (F : R[M] →ₐ[R] A) :
    F = AddMonoidAlgebra.lift R A M ((F : R[M] →* A).comp (of R M)) := ((AddMonoidAlgebra.lift R A M).apply_symm_apply F).symm

