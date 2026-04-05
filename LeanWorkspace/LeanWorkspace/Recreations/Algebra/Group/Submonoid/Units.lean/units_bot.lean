import Mathlib

variable {M : Type*} [Monoid M]

theorem units_bot : (⊥ : Submonoid M).units = ⊥ := ofUnits_units_gci.u_bot

