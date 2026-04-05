import Mathlib

variable {ι α β M N G k R : Type*}

variable [DecidableEq α] {s : Finset α} {B : Finset (Finset α)} {n : ℕ}

theorem card_le_card_biUnion_add_one {s : Finset ι} {f : ι → Finset α} (hf : Function.Injective f)
    (hs : (s : Set ι).PairwiseDisjoint f) : #s ≤ #(s.biUnion f) + 1 := by
  grw [Finset.card_le_card_biUnion_add_card_fiber hs,
    card_le_one.2 fun _ hi _ hj ↦ hf <| (mem_filter.1 hi).2.trans (mem_filter.1 hj).2.symm]

