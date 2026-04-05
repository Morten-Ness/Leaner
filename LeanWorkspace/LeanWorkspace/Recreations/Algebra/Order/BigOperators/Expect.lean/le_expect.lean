import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

variable [PosSMulMono ℚ≥0 α] {a : α}

theorem le_expect (hs : s.Nonempty) (h : ∀ x ∈ s, a ≤ f x) : a ≤ 𝔼 i ∈ s, f i := (le_inv_smul_iff_of_pos <| mod_cast hs.card_pos).2 <| by
    rw [Nat.cast_smul_eq_nsmul]; exact card_nsmul_le_sum _ _ _ h

