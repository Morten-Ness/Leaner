import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f : ι → α}

variable [PosSMulStrictMono ℚ≥0 α]

theorem expect_pos (hf : ∀ i ∈ s, 0 < f i) (hs : s.Nonempty) : 0 < 𝔼 i ∈ s, f i := smul_pos (inv_pos.2 <| mod_cast hs.card_pos) <| sum_pos hf hs

