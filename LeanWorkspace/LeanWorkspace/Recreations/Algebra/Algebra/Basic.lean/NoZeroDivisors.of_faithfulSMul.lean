import Mathlib

open scoped Algebra

variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

theorem NoZeroDivisors.of_faithfulSMul [NoZeroDivisors A] : NoZeroDivisors R := (FaithfulSMul.algebraMap_injective R A).noZeroDivisors _ (by simp) (by simp)

