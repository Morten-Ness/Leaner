import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_singleton : (∏ᶠ i ∈ ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton, finprod_mem_coe_finset, Finset.prod_singleton]

