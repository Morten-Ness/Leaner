import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_normalClosure : s ⊆ Subgroup.normalClosure s := Set.Subset.trans Group.subset_conjugatesOfSet Subgroup.conjugatesOfSet_subset_normalClosure

