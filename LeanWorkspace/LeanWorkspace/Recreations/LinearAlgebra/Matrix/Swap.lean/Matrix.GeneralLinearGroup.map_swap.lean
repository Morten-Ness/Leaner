import Mathlib

variable (R : Type*) {n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

theorem map_swap (i j : n) : (Matrix.GeneralLinearGroup.swap R i j).map f = Matrix.GeneralLinearGroup.swap S i j := by
  ext : 1
  simp [Matrix.GeneralLinearGroup.swap]

