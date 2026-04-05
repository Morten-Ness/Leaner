import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_permute_rows (σ : Equiv.Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).permanent = M.permanent := by
  rw [← Matrix.permanent_transpose, transpose_submatrix, Matrix.permanent_permute_cols, Matrix.permanent_transpose]

