import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x ∈ H.units ↔ x ∈ H := by
  simp_rw [Subgroup.mem_units_iff_val_mem, val_toUnits_apply]

