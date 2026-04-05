import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_eq_one_iff {r : R} : algebraMap R A r = 1 ↔ r = 1 := by
  constructor
  · intro h
    apply FaithfulSMul.algebraMap_injective R A
    simpa using h
  · intro h
    simp [h]
