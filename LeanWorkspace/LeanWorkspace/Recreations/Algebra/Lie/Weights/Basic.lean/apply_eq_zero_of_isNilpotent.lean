import Mathlib

variable {K R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [LieRing.IsNilpotent L]

theorem apply_eq_zero_of_isNilpotent [IsDomain R] [Module.IsTorsionFree R M] [IsReduced R]
    (x : L) (h : _root_.IsNilpotent (toEnd R L M x)) (χ : LieModule.Weight R L M) :
    χ x = 0 := ((χ.hasEigenvalueAt x).isNilpotent_of_isNilpotent h).eq_zero

