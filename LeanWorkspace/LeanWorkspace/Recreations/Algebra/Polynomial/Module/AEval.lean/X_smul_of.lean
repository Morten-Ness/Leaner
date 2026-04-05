import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

theorem X_smul_of (m : M) : (Polynomial.X : R[X]) • (Module.AEval.of R M a m) = Module.AEval.of R M a (a • m) := by
  rw [← Module.AEval.of_aeval_smul, aeval_X]

