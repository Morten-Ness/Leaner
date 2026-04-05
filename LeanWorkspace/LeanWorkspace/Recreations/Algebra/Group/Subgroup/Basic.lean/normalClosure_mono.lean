import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_mono {s t : Set G} (h : s ⊆ t) : Subgroup.normalClosure s ≤ Subgroup.normalClosure t := Subgroup.normalClosure_le_normal (Set.Subset.trans h Subgroup.subset_normalClosure)

