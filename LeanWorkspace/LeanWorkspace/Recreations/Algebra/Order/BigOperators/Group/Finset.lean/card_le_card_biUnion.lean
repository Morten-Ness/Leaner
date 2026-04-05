import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem card_le_card_biUnion {s : Finset ι} {f : ι → Finset α} (hs : (s : Set ι).PairwiseDisjoint f)
    (hf : ∀ i ∈ s, (f i).Nonempty) : #s ≤ #(s.biUnion f) := by
  rw [card_biUnion hs, card_eq_sum_ones]
  exact sum_le_sum fun i hi ↦ (hf i hi).card_pos

