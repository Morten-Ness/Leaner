import Mathlib

variable {M : Type*} [Monoid M]

theorem units_sInf {s : Set (Submonoid M)} : (sInf s).units = ⨅ S ∈ s, S.units := ofUnits_units_gc.u_sInf

