import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_ne_bot (H : Subgroup G) : Nontrivial H ↔ H ≠ ⊥ := by
  simpa using Subgroup.nontrivial_iff_ne_bot H
