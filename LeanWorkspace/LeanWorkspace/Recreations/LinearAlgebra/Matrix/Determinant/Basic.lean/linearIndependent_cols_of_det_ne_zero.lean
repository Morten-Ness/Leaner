import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem linearIndependent_cols_of_det_ne_zero [IsDomain R] {A : Matrix m m R} (hA : A.det ≠ 0) :
    LinearIndependent R A.col := Matrix.linearIndependent_rows_of_det_ne_zero (by simpa [Matrix.col])

