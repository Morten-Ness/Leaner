import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem pow_card_le_prod [MulLeftMono α] (h : ∀ x ∈ s, a ≤ x) : a ^ card s ≤ s.prod := by
  rw [← Multiset.prod_replicate, ← Multiset.map_const]
  exact Multiset.prod_map_le_prod _ h

