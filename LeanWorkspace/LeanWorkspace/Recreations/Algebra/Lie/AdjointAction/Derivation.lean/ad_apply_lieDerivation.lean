import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem ad_apply_lieDerivation (x : L) (D : LieDerivation R L L) : LieDerivation.ad R L (D x) = -⁅x, D⁆ := rfl

