import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_iSup {ι : Sort*} {f : ι → Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := ofUnits_units_gc.l_iSup

