import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem nonempty_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : s.Nonempty := by
  by_contra hs
  rw [Finset.not_nonempty_iff_eq_empty] at hs
  subst hs
  simpa using h
