import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_of_le (h₁ : k ⊆ K) (h₂ : K ≤ Subgroup.closure k) : Subgroup.closure k = K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact h₁
  · exact h₂
