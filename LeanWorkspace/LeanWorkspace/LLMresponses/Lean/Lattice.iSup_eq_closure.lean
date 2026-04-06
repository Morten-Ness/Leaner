FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem iSup_eq_closure {ι : Sort*} (p : ι → Subgroup G) :
    ⨆ i, p i = Subgroup.closure (⋃ i, (p i : Set G)) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    refine Subgroup.closure_mono ?_
    exact Set.subset_iUnion (fun j => (p j : Set G)) i
  · rw [Subgroup.closure_eq]
    exact le_iSup (fun i => p i) x
