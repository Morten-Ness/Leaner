import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_le : Subgroup.closure k ≤ K ↔ k ⊆ K := ⟨Subset.trans Subgroup.subset_closure, fun h => sInf_le h⟩

