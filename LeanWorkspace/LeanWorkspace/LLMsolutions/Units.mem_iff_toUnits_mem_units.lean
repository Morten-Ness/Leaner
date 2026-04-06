import Mathlib

variable {M : Type*} [Monoid M]

variable {G : Type*} [Group G]

theorem mem_iff_toUnits_mem_units (H : Subgroup G) (x : G) : toUnits x ∈ H.units ↔ x ∈ H := by
  change x ∈ H ∧ ↑(↑(toUnits x)⁻¹) ∈ H ↔ x ∈ H
  simp
