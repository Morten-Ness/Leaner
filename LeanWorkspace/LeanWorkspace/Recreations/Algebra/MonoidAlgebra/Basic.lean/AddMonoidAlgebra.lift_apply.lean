import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_apply (F : Multiplicative M →* A) (f : R[M]) :
    AddMonoidAlgebra.lift R A M F f = f.sum fun a b => b • F (Multiplicative.ofAdd a) := by
  simp only [AddMonoidAlgebra.lift_apply', Algebra.smul_def]

