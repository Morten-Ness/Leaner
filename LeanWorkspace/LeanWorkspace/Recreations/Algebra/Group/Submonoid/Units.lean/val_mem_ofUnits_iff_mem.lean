import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem val_mem_ofUnits_iff_mem (H : Subgroup Gˣ) (x : Gˣ) : (x : G) ∈ H.ofUnits ↔ x ∈ H := by
  simp_rw [Subgroup.mem_ofUnits_iff_toUnits_mem, toUnits_val_apply]

