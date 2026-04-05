import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_units_iff_val_mem (H : Subgroup G) (x : Gˣ) : x ∈ H.units ↔ (x : G) ∈ H := by
  simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, val_inv_eq_inv_val, inv_mem_iff, and_self]

