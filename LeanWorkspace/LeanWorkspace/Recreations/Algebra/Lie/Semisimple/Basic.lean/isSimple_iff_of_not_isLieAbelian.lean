import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

set_option backward.isDefEq.respectTransparency false in
theorem isSimple_iff_of_not_isLieAbelian (hL : ¬ IsLieAbelian L) :
    IsSimpleOrder (LieIdeal R L) ↔ IsSimple R L := ⟨fun _ ↦ ⟨IsSimpleOrder.eq_bot_or_eq_top, hL⟩, fun _ ↦ inferInstance⟩

