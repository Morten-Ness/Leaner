import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

theorem apply_lie_eq_add (D : LieDerivation R L L) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ + ⁅D a, b⁆ := by
  rw [LieDerivation.apply_lie_eq_sub, sub_eq_add_neg, lie_skew]

