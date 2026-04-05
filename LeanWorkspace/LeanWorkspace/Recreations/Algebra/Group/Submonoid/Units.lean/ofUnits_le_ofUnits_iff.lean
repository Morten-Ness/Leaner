import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_le_ofUnits_iff {S T : Subgroup Mˣ} : S.ofUnits ≤ T.ofUnits ↔ S ≤ T := ofUnits_units_gci.l_le_l_iff

