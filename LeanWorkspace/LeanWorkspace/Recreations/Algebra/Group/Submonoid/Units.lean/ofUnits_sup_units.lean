import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_sup_units (S T : Subgroup Mˣ) : (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T := ofUnits_units_gci.u_sup_l _ _

