import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_permute' (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix id σ).det = Perm.sign σ * M.det := by
  rw [← Matrix.det_transpose, transpose_submatrix, Matrix.det_permute, Matrix.det_transpose]

