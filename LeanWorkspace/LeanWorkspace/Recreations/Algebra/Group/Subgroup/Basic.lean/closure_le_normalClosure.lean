import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem closure_le_normalClosure {s : Set G} : closure s ≤ Subgroup.normalClosure s := by
  simp only [Subgroup.subset_normalClosure, closure_le]

