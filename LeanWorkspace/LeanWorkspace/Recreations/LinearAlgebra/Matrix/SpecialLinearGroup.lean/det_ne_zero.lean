import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable (A B : SpecialLinearGroup n R)

theorem det_ne_zero [Nontrivial R] (g : Matrix.SpecialLinearGroup n R) : det ↑ₘg ≠ 0 := by
  rw [Matrix.SpecialLinearGroup.det_coe g]
  norm_num

