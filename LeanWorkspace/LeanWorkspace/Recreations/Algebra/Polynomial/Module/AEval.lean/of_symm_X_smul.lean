import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

theorem of_symm_X_smul (m : Module.AEval R M a) :
    (Module.AEval.of R M a).symm ((Polynomial.X : R[X]) • m) = a • (Module.AEval.of R M a).symm m := by
  rw [of_symm_smul, aeval_X]

