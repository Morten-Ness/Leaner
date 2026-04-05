import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem bot_or_nontrivial (H : Subgroup G) : H = ⊥ ∨ Nontrivial H := by
  have := Subgroup.nontrivial_iff_ne_bot H
  tauto

