import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [AddMonoidAlgebra.lift_unique' F]
    simp [AddMonoidAlgebra.lift_apply]

