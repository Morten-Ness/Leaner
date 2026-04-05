import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_inf_units (S T : Subgroup Mˣ) : (S.ofUnits ⊓ T.ofUnits).units = S ⊓ T := ofUnits_units_gci.u_inf_l _ _

