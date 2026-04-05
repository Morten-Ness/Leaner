import Mathlib

open scoped Algebra

variable {R : Type*} [CommSemiring R]

variable (A : Type*) [Semiring A] [Algebra R A]

variable {M : Type*} [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_one, one_smul]

