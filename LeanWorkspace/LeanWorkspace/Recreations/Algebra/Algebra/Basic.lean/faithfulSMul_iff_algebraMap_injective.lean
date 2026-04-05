import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

theorem faithfulSMul_iff_algebraMap_injective : FaithfulSMul R A ↔ Function.Injective (algebraMap R A) := by
  rw [faithfulSMul_iff_injective_smul_one, Algebra.algebraMap_eq_smul_one']

