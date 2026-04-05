import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

variable [PosSMulMono ℚ≥0 α] {a : α}

theorem expect_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ 𝔼 i ∈ s, f i := smul_nonneg (by positivity) <| sum_nonneg hf

