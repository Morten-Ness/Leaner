import Mathlib

variable {M : Type*} [Monoid M]

theorem inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : x⁻¹ ∈ S.units := inv_mem h

