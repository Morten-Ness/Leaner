import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem mem_ad_idealRange_iff {D : LieDerivation R L L} :
    D ∈ (LieDerivation.ad R L).idealRange ↔ ∃ x : L, LieDerivation.ad R L x = D := (LieDerivation.ad R L).mem_idealRange_iff (LieDerivation.ad_isIdealMorphism R L)

