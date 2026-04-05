import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem eq_bot_of_subsingleton [Subsingleton H] : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [← Subgroup.coe_mk H y hy, Subsingleton.elim (⟨y, hy⟩ : H) 1, Subgroup.coe_one]

