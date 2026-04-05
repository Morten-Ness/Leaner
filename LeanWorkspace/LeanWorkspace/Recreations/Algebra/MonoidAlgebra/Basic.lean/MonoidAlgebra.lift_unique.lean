import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_unique (F : R[M] →ₐ[R] A) (f : R[M]) :
    F f = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [MonoidAlgebra.lift_unique' F]
    simp [MonoidAlgebra.lift_apply]

