import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateCol_add (M : Matrix n n R) (j : n) (u v : n → R) :
    Matrix.det (updateCol M j <| u + v) = Matrix.det (updateCol M j u) + Matrix.det (updateCol M j v) := by
  rw [← Matrix.det_transpose, ← updateRow_transpose, Matrix.det_updateRow_add]
  simp [updateRow_transpose, Matrix.det_transpose]

