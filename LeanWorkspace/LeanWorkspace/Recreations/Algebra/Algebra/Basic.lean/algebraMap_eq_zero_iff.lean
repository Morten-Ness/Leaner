import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_eq_zero_iff {r : R} : algebraMap R A r = 0 ↔ r = 0 := map_eq_zero_iff (algebraMap R A) <| FaithfulSMul.algebraMap_injective R A

