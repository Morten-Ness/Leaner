import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [Fintype ι]

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α] {f : ι → α}

theorem expect_eq_zero_iff_of_nonpos (hf : f ≤ 0) : 𝔼 i, f i = 0 ↔ f = 0 := by
  rw [Finset.expect_eq_zero_iff_of_nonpos (by aesop)]
  aesop

