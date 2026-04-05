import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, LieDerivation.ad R L x⁆ = LieDerivation.ad R L (D x) := by
  rw [LieDerivation.ad_apply_lieDerivation, ← LieDerivation.lie_ad, lie_skew]

