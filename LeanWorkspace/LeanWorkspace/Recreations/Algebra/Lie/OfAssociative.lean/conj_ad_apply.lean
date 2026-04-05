import Mathlib

variable {R L L' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

theorem conj_ad_apply (e : L ≃ₗ⁅R⁆ L') (x : L) : e.toLinearEquiv.conj (ad R L x) = ad R L' (e x) := by
  ext y'
  rw [LinearEquiv.conj_apply_apply, ad_apply, ad_apply, coe_toLinearEquiv, map_lie,
    ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]

