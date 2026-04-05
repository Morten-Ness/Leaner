import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L]
  (D : LieDerivation R L L)

theorem exp_map_apply (h : IsNilpotent D.toLinearMap) (l : L) :
    LieDerivation.exp D h l = IsNilpotent.exp D.toLinearMap l := DFunLike.congr_fun (LieDerivation.exp_apply D h) l

