import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 := algebraMap.coe_eq_zero_iff _ _ _

