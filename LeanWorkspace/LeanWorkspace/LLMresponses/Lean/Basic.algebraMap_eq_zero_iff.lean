FAIL
import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0 := by
  constructor
  · intro h
    have h' : r • (1 : A) = 0 := by
      simpa [Algebra.algebraMap_eq_smul_one] using h
    exact (smul_eq_zero.mp h').resolve_right one_ne_zero
  · intro h
    simp [h]
