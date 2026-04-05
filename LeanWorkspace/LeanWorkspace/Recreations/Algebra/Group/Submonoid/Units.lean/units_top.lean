import Mathlib

variable {M : Type*} [Monoid M]

theorem units_top : (⊤ : Submonoid M).units = ⊤ := ofUnits_units_gc.u_top

