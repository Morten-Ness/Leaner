import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_diff_one (s : Set G) : Subgroup.closure (s \ {1}) = Subgroup.closure s := by
  rw [← Subgroup.closure_union_one (s \ {1}), diff_union_self, Subgroup.closure_union_one]

