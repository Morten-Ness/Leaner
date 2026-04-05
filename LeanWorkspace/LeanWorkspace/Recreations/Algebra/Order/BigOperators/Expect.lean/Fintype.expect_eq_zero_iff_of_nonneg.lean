import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [Fintype ι]

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] {f : ι → α}

theorem expect_eq_zero_iff_of_nonneg (hf : 0 ≤ f) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonneg (by aesop)]
  aesop

