import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable (A B : SpecialLinearGroup n R)

theorem row_ne_zero [Nontrivial R] (g : Matrix.SpecialLinearGroup n R) (i : n) : g i ≠ 0 := fun h =>
  Matrix.SpecialLinearGroup.det_ne_zero g <| det_eq_zero_of_row_eq_zero i <| by simp [h]

