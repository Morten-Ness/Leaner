import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem le_normalClosure {H : Subgroup G} : H ≤ Subgroup.normalClosure ↑H := by
  intro h hh
  exact Subgroup.subset_normalClosure hh
