import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

variable [PosSMulMono ℚ≥0 α] {a : α}

theorem expect_le (hs : s.Nonempty) (h : ∀ x ∈ s, f x ≤ a) : 𝔼 i ∈ s, f i ≤ a := (inv_smul_le_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact sum_le_card_nsmul _ _ _ h

