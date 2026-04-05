import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

theorem toLin'_to_linearMap (A : Matrix.SpecialLinearGroup n R) :
    ↑(Matrix.SpecialLinearGroup.toLin' A) = Matrix.toLin' ↑ₘA := rfl

