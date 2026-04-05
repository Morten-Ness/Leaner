import Mathlib

open scoped Algebra

variable (R S A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A]

theorem IsCancelMulZero.of_faithfulSMul [IsCancelMulZero A] : IsCancelMulZero R := (FaithfulSMul.algebraMap_injective R A).isCancelMulZero _ (by simp) (by simp)

