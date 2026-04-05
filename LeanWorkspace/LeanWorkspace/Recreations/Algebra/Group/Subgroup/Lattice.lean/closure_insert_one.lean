import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_insert_one (s : Set G) : Subgroup.closure (insert 1 s) = Subgroup.closure s := by
  rw [insert_eq, Subgroup.closure_union]
  simp [one_mem]

