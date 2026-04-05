import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem det_mapGL (g : Matrix.SpecialLinearGroup n R) : (Matrix.SpecialLinearGroup.mapGL S g).det = 1 := by
  simp [Matrix.SpecialLinearGroup.mapGL]

