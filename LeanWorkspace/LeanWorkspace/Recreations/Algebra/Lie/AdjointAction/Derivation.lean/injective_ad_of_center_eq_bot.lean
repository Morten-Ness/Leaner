import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem injective_ad_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    Function.Injective (LieDerivation.ad R L) := by
  rw [← LieHom.ker_eq_bot, LieDerivation.ad_ker_eq_center, h]

