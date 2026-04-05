import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugatesOfSet_subset_normalClosure : Group.conjugatesOfSet s ⊆ Subgroup.normalClosure s := subset_closure

