import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem add_apply_apply (a b : LieModule.Cohomology.twoCochain R L M) (x y : L) :
    (a + b) x y = a x y + b x y := by
  rfl

