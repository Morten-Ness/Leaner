import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_smul (A : Matrix n n R) (c : R) : Matrix.det (c • A) = c ^ Fintype.card n * Matrix.det A := calc
    Matrix.det (c • A) = Matrix.det ((diagonal fun _ => c) * A) := by rw [smul_eq_diagonal_mul]
    _ = Matrix.det (diagonal fun _ => c) * Matrix.det A := Matrix.det_mul _ _
    _ = c ^ Fintype.card n * Matrix.det A := by simp

