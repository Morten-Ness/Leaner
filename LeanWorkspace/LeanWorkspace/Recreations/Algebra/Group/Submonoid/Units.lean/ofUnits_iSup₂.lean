import Mathlib

variable {M : Type*} [Monoid M]

theorem ofUnits_iSup₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Subgroup Mˣ) :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits := ofUnits_units_gc.l_iSup₂

