import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  [PosSMulMono ℚ≥0 α] {s : Finset ι}
  {f : ι → α} {a : α}

theorem exists_lt_of_lt_expect (hs : s.Nonempty) (h : a < 𝔼 i ∈ s, f i) : ∃ x ∈ s, a < f x := by
  contrapose! h; exact Finset.expect_le hs h

