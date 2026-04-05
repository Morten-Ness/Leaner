import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem nonempty_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : s.Nonempty := nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ finprod_mem_empty

