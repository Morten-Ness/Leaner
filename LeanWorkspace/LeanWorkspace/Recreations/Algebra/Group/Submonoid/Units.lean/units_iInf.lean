import Mathlib

variable {M : Type*} [Monoid M]

theorem units_iInf {ι : Sort*} (f : ι → Submonoid M) : (iInf f).units = ⨅ (i : ι), (f i).units := ofUnits_units_gc.u_iInf

