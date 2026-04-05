import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_one (s : Set α) : (∏ᶠ i ∈ s, (1 : M)) = 1 := by simp

