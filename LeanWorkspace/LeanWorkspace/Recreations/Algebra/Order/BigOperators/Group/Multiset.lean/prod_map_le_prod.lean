import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem prod_map_le_prod [MulLeftMono α] (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) :
    (s.map f).prod ≤ s.prod := Multiset.prod_le_prod_of_rel_le <| rel_map_left.2 <| rel_refl_of_refl_on h

