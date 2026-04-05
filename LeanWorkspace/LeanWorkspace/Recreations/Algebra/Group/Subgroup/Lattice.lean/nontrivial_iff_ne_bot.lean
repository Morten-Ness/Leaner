import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem nontrivial_iff_ne_bot (H : Subgroup G) : Nontrivial H ↔ H ≠ ⊥ := by
  rw [Subgroup.nontrivial_iff_exists_ne_one, ne_eq, Subgroup.eq_bot_iff_forall]
  simp only [ne_eq, not_forall, exists_prop]

