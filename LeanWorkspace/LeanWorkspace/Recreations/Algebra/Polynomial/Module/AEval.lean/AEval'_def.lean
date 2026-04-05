import Mathlib

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

variable (φ : M →ₗ[R] M)

theorem AEval'_def : AEval' φ = Module.AEval R M φ := rfl

