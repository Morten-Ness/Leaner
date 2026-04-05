import Mathlib

open scoped Polynomial

variable {R A M} [CommSemiring R] [Semiring A] (a : A) [Algebra R A] [AddCommMonoid M] [Module A M]
  [Module R M] [IsScalarTower R A M]

variable (φ : M →ₗ[R] M)

theorem AEval'.of_symm_X_smul (m : AEval' φ) :
    (AEval'.of φ).symm ((Polynomial.X : R[X]) • m) = φ ((AEval'.of φ).symm m) := Module.AEval.of_symm_X_smul _ _

