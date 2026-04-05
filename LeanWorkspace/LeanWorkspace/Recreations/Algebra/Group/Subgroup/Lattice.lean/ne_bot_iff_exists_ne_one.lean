import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem ne_bot_iff_exists_ne_one {H : Subgroup G} : H ≠ ⊥ ↔ ∃ a : ↥H, a ≠ 1 := by
  rw [← Subgroup.nontrivial_iff_ne_bot, Subgroup.nontrivial_iff_exists_ne_one]
  simp only [ne_eq, Subtype.exists, mk_eq_one, exists_prop]

