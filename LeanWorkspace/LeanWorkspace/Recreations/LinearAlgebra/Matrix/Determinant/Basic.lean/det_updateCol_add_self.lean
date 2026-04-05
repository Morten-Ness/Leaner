import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateCol_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    Matrix.det (updateCol A i fun k => A k i + A k j) = Matrix.det A := by
  rw [← Matrix.det_transpose, ← updateRow_transpose, ← Matrix.det_transpose A]
  exact Matrix.det_updateRow_add_self Aᵀ hij

