import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.col ↔ IsUnit A := by
  rw [← row_transpose, Matrix.linearIndependent_rows_iff_isUnit, isUnit_transpose]

