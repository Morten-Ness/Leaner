import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  (D : LieDerivation R L L)

theorem exp_apply (h : IsNilpotent D.toLinearMap) :
    LieDerivation.exp D h = IsNilpotent.exp D.toLinearMap := rfl

