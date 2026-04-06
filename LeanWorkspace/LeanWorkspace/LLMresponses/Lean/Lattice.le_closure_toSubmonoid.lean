import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem le_closure_toSubmonoid (S : Set G) : Submonoid.closure S ≤ (Subgroup.closure S).toSubmonoid := by
  rw [Submonoid.closure_le]
  intro x hx
  exact Subgroup.subset_closure hx
