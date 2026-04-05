import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem coe_GL_coe_matrix (g : Matrix.SpecialLinearGroup n R) : ((Matrix.SpecialLinearGroup.toGL g) : Matrix n n R) = g := rfl

