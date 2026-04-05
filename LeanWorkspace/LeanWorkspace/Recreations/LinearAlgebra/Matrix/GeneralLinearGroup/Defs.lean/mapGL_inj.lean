import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem mapGL_inj [FaithfulSMul R S] (g g' : Matrix.SpecialLinearGroup n R) :
    Matrix.SpecialLinearGroup.mapGL S g = Matrix.SpecialLinearGroup.mapGL S g' ↔ g = g' := by
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.GeneralLinearGroup.ext_iff]

