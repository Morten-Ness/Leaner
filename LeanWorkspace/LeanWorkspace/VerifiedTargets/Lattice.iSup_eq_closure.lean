import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem iSup_eq_closure {ι : Sort*} (p : ι → Subgroup G) :
    ⨆ i, p i = Subgroup.closure (⋃ i, (p i : Set G)) := by simp_rw [Subgroup.closure_iUnion, Subgroup.closure_eq]

