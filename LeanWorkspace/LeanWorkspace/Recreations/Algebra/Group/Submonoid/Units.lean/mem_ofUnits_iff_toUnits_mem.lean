import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_ofUnits_iff_toUnits_mem (H : Subgroup Gˣ) (x : G) : x ∈ H.ofUnits ↔ (toUnits x) ∈ H := by
  simp_rw [Subgroup.mem_ofUnits_iff, toUnits.surjective.exists, val_toUnits_apply, exists_eq_right]

