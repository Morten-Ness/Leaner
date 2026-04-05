import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a := finprod_mem_singleton

