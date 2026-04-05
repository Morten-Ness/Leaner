import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem prod_map_le_prod_map [MulLeftMono α] {s : Multiset ι} (f : ι → α) (g : ι → α)
    (h : ∀ i, i ∈ s → f i ≤ g i) : (s.map f).prod ≤ (s.map g).prod := Multiset.prod_le_prod_of_rel_le <| rel_map.2 <| rel_refl_of_refl_on h

