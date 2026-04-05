import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem smul_apply_apply (r : R) (a : LieModule.Cohomology.twoCochain R L M) (x y : L) :
    (r • a) x y = r • (a x y) := by
  rfl

