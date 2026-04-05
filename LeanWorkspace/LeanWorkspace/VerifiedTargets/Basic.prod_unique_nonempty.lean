import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι → M) (h : s.Nonempty) :
    ∏ x ∈ s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]

