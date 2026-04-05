import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem twoCochain_val_apply (a : LieModule.Cohomology.twoCochain R L M) (x : L) :
    a.val x = a x := rfl

