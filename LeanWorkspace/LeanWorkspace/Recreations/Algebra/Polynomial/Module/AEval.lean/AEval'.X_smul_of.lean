import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

variable (φ : M →ₗ[R] M)

theorem AEval'.X_smul_of (m : M) : (Polynomial.X : R[X]) • AEval'.of φ m = AEval'.of φ (φ m) := Module.AEval.X_smul_of _ _

