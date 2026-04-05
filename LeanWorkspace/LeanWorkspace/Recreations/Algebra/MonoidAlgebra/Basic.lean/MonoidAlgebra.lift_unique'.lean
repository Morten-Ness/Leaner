import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_unique' (F : R[M] →ₐ[R] A) : F = MonoidAlgebra.lift R A M ((F : R[M] →* A).comp (of R M)) := ((MonoidAlgebra.lift R A M).apply_symm_apply F).symm

