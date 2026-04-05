import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    Matrix.det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * Matrix.det (A.submatrix Fin.succ j.succAbove) := by
  rw [← Matrix.det_transpose A, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.det_transpose]
  simp only [transpose_apply, transpose_submatrix, transpose_transpose]

