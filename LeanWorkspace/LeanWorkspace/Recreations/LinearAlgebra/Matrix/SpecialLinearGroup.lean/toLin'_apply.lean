import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

theorem toLin'_apply (A : Matrix.SpecialLinearGroup n R) (v : n → R) :
    Matrix.SpecialLinearGroup.toLin' A v = Matrix.toLin' (↑ₘA) v := rfl

