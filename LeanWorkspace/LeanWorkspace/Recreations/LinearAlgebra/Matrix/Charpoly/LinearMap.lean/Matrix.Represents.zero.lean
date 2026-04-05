import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by
  delta Matrix.Represents
  rw [map_zero, map_zero]

