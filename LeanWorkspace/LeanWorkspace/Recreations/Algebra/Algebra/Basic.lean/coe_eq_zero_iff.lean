import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem coe_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 := FaithfulSMul.algebraMap_eq_zero_iff _ _

