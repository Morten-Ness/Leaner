import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem single_le_prod [IsOrderedMonoid α] : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod := Quotient.inductionOn s fun l hl x hx => by simpa using List.single_le_prod hl x hx

