import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_bot_iff : Subgroup.closure k = ⊥ ↔ k ⊆ {1} := by
  constructor
  · intro h x hx
    have hx' : x ∈ (Subgroup.closure k : Subgroup G) := Subgroup.subset_closure hx
    rw [h] at hx'
    simpa using hx'
  · intro h
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      have hx1 : x = 1 := by simpa using h hx
      simpa [hx1]
    · exact bot_le
