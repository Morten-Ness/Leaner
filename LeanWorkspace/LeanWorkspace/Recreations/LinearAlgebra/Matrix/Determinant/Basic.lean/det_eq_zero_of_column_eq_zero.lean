import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_zero_of_column_eq_zero {A : Matrix n n R} (j : n) (h : ∀ i, A i j = 0) :
    Matrix.det A = 0 := by
  rw [← Matrix.det_transpose]
  exact Matrix.det_eq_zero_of_row_eq_zero j h

