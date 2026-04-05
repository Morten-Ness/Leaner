import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem le_normalClosure {H : Subgroup G} : H ≤ Subgroup.normalClosure ↑H := fun _ h =>
  Subgroup.subset_normalClosure h

