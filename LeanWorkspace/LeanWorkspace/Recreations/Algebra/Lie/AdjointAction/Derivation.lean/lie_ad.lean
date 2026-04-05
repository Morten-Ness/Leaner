import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem lie_ad (x : L) (D : LieDerivation R L L) : ⁅LieDerivation.ad R L x, D⁆ = ⁅x, D⁆ := by ext; simp

