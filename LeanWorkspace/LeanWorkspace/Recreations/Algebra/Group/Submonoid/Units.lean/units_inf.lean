import Mathlib

variable {M : Type*} [Monoid M]

theorem units_inf (S T : Submonoid M) : (S ⊓ T).units = S.units ⊓ T.units := ofUnits_units_gc.u_inf

