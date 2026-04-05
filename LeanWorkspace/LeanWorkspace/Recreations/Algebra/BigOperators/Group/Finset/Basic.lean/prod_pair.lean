import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_pair [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    (∏ x ∈ ({a, b} : Finset ι), f x) = f a * f b := by
  rw [Finset.prod_insert (notMem_singleton.2 h), Finset.prod_singleton]

