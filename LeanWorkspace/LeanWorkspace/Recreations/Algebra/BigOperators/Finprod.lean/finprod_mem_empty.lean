import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_empty : (∏ᶠ i ∈ (∅ : Set α), f i) = 1 := by simp

