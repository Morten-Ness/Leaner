import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem one_le_prod_of_one_le [MulLeftMono α] : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod := Quotient.inductionOn s fun l hl => by simpa using List.one_le_prod_of_one_le hl

