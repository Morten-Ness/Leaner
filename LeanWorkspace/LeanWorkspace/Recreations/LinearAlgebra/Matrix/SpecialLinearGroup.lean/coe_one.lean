import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable (A B : SpecialLinearGroup n R)

theorem coe_one : (1 : Matrix.SpecialLinearGroup n R) = (1 : Matrix n n R) := rfl

