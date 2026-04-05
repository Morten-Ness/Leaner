import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s ⊆ N ↔ Subgroup.normalClosure s ≤ N := ⟨Subgroup.normalClosure_le_normal, Set.Subset.trans Subgroup.subset_normalClosure⟩

