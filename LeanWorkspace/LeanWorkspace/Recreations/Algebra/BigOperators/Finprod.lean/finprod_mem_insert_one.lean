import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_insert_one (h : f a = 1) : ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i := finprod_mem_insert_of_eq_one_if_notMem fun _ => h

