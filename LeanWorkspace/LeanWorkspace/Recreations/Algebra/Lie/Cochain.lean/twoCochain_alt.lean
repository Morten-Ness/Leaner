import Mathlib

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable (M : Type*) [AddCommGroup M] [Module R M]

theorem twoCochain_alt (a : LieModule.Cohomology.twoCochain R L M) (x : L) :
    a x x = 0 := a.2 x

