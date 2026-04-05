import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_or_exists_ne_one (H : Subgroup G) : H = ⊥ ∨ ∃ x ∈ H, x ≠ (1 : G) := by
  convert H.bot_or_nontrivial
  rw [Subgroup.nontrivial_iff_exists_ne_one]

