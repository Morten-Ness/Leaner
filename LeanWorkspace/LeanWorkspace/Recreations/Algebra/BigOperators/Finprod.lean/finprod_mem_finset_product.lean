import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (_ : ab ∈ s), f ab) = ∏ᶠ (a) (b) (_ : (a, b) ∈ s), f (a, b) := by
  classical
    rw [finprod_mem_finset_product']
    simp

