import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem ad_isIdealMorphism : (LieDerivation.ad R L).IsIdealMorphism := by
  simp_rw [LieHom.isIdealMorphism_iff, LieDerivation.lie_der_ad_eq_ad_der]
  tauto

