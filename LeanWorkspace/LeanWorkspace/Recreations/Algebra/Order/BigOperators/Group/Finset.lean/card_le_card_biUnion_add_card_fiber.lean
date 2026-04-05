import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem card_le_card_biUnion_add_card_fiber {s : Finset ι} {f : ι → Finset α}
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + #{i ∈ s | f i = ∅} := by
  rw [← Finset.card_filter_add_card_filter_not fun i ↦ f i = ∅, add_comm]
  grw [Finset.card_le_card_biUnion (hs.subset <| filter_subset _ _) fun i hi ↦
    nonempty_of_ne_empty (mem_filter.1 hi).2, filter_subset]

