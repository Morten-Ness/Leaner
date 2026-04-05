import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι}
  {f : ι → α} {a : α}

theorem exists_lt_of_expect_lt (hs : s.Nonempty) (h : 𝔼 i ∈ s, f i < a) : ∃ x ∈ s, f x < a := by
  contrapose! h; exact Finset.le_expect hs h

