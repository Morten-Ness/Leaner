import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

theorem ext (A B : Matrix.SpecialLinearGroup n R) : (∀ i j, A i j = B i j) → A = B := (Matrix.SpecialLinearGroup.ext_iff A B).mpr

