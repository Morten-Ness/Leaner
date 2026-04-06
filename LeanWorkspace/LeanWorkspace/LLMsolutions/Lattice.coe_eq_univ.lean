import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.univ ↔ H = ⊤ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      have : x ∈ (H : Set G) := by
        rw [h]
        simp
      exact this
  · intro h
    rw [h]
    ext x
    simp
