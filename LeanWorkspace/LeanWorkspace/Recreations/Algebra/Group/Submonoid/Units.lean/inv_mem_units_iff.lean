import Mathlib

variable {M : Type*} [Monoid M]

theorem inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ ∈ S.units ↔ x ∈ S.units := inv_mem_iff

