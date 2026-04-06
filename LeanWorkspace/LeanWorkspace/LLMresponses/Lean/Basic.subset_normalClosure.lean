import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_normalClosure : s ⊆ Subgroup.normalClosure s := by
  intro x hx
  exact Subgroup.subset_normalClosure hx
