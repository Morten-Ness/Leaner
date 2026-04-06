import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_top_iff' : H = ⊤ ↔ ∀ x : G, x ∈ H := by
  constructor
  · intro h x
    rw [h]
    trivial
  · intro h
    ext x
    constructor
    · intro hx
      trivial
    · intro hx
      exact h x
