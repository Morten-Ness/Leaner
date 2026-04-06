FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_top_of_mclosure_eq_top {S : Set G} (h : Submonoid.closure S = ⊤) :
    Subgroup.closure S = ⊤ := by
  ext g
  constructor
  · intro _
    trivial
  · intro _
    have hg : g ∈ Submonoid.closure S := by
      rw [h]
      exact Submonoid.mem_top g
    exact Subgroup.closure_le.2
      (show ((S : Set G) ⊆ (Subgroup.closure S : Set G)) from Subgroup.subset_closure) hg
