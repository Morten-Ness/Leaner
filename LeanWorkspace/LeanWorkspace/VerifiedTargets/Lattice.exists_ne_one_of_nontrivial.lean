import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem exists_ne_one_of_nontrivial (H : Subgroup G) [Nontrivial H] :
    ∃ x ∈ H, x ≠ 1 := by
  rwa [← Subgroup.nontrivial_iff_exists_ne_one]

