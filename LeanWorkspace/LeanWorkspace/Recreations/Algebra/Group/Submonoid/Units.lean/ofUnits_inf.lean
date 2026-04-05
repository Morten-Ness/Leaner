import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_inf (S T : Subgroup Mˣ) : (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits := ofUnits_units_gc.l_sup

