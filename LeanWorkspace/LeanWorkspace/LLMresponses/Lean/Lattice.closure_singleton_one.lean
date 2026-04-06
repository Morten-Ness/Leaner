import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_singleton_one : Subgroup.closure ({1} : Set G) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Subgroup.closure_le]
  intro x hx
  simp at hx
  simp [hx]
