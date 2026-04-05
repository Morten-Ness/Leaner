import Mathlib

variable {M : Type*} [Monoid M]

theorem units_iInf₂ {ι : Sort*} {κ : ι → Sort*} (f : (i : ι) → κ i → Submonoid M) :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units := ofUnits_units_gc.u_iInf₂

