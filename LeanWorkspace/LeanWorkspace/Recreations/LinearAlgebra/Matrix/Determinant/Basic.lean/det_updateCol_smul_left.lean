import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateCol_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    Matrix.det (updateCol (s • M) j u) = s ^ (Fintype.card n - 1) * Matrix.det (updateCol M j u) := by
  rw [← Matrix.det_transpose, ← updateRow_transpose, transpose_smul, Matrix.det_updateRow_smul_left]
  simp [updateRow_transpose, Matrix.det_transpose]

