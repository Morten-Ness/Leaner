import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem coe_to_GLPos_to_GL_det (g : Matrix.SpecialLinearGroup n R) :
    Matrix.GeneralLinearGroup.det ((g : Matrix.GLPos n R) : GL n R) = 1 := Units.ext g.prop

