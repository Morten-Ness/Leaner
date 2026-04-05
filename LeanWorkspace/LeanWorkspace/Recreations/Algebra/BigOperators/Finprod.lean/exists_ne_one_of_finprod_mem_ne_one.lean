import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem exists_ne_one_of_finprod_mem_ne_one (h : ∏ᶠ i ∈ s, f i ≠ 1) : ∃ x ∈ s, f x ≠ 1 := by
  by_contra! h'
  exact h (finprod_mem_of_eqOn_one h')

