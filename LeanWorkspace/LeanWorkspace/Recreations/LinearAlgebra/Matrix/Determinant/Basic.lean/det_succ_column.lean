import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_succ_column {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (j : Fin n.succ) :
    Matrix.det A =
      ∑ i : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * Matrix.det (A.submatrix i.succAbove j.succAbove) := by
  rw [← Matrix.det_transpose, Matrix.det_succ_row _ j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, ← Matrix.det_transpose, transpose_apply, transpose_submatrix, transpose_transpose]

