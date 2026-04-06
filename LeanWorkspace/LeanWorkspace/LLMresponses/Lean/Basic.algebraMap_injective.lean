import Mathlib

open scoped Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]

variable [FaithfulSMul R A]

theorem algebraMap_injective : Function.Injective (algebraMap R A) := by
  intro x y h
  apply FaithfulSMul.algebraMap_injective (R := R) (A := A)
  exact h
