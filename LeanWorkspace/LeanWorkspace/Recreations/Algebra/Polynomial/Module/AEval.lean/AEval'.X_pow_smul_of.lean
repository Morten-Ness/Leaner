import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

variable (φ : M →ₗ[R] M)

theorem AEval'.X_pow_smul_of (m : M) (n : ℕ) : (Polynomial.X ^ n : R[X]) • AEval'.of φ m = .of φ (φ ^ n • m) := Module.AEval.X_pow_smul_of ..

