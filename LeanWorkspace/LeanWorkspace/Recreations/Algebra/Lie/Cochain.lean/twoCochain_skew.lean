import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem twoCochain_skew (a : LieModule.Cohomology.twoCochain R L M) (x y : L) : - a x y = a y x := by
  rw [neg_eq_iff_add_eq_zero, add_comm]
  simpa [map_add, LieModule.Cohomology.twoCochain_alt a x, LieModule.Cohomology.twoCochain_alt a y] using LieModule.Cohomology.twoCochain_alt a (x + y)

