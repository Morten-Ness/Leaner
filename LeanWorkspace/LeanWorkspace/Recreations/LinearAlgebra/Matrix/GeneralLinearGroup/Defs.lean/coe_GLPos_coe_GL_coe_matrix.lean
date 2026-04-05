import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem coe_GLPos_coe_GL_coe_matrix (g : Matrix.SpecialLinearGroup n R) :
    (↑(↑(↑g : Matrix.GLPos n R) : GL n R) : Matrix n n R) = ↑g := rfl

