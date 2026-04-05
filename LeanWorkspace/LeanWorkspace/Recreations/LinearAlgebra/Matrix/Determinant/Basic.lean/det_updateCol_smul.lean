import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateCol_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    Matrix.det (updateCol M j <| s • u) = s * Matrix.det (updateCol M j u) := by
  rw [← Matrix.det_transpose, ← updateRow_transpose, Matrix.det_updateRow_smul]
  simp [updateRow_transpose, Matrix.det_transpose]

