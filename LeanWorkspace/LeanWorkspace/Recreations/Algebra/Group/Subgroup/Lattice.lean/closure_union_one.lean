import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_union_one (s : Set G) : Subgroup.closure (s ∪ {1}) = Subgroup.closure s := by
  rw [union_singleton, Subgroup.closure_insert_one]

