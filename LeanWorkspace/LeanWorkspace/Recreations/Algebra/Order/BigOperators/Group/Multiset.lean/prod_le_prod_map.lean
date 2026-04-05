import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem prod_le_prod_map [MulLeftMono α] (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) :
    s.prod ≤ (s.map f).prod := Multiset.prod_map_le_prod (α := αᵒᵈ) f h

