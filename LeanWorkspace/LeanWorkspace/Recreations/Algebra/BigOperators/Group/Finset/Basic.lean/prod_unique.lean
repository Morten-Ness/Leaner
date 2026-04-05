import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_unique [Unique ι] (f : ι → M) : ∏ x : ι, f x = f default := by
  rw [univ_unique, Finset.prod_singleton]

