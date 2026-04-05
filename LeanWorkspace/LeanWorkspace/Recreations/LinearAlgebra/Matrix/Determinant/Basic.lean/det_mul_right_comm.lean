import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul_right_comm (M N P : Matrix m m R) : Matrix.det (M * N * P) = Matrix.det (M * P * N) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_mul_comm N P, ← Matrix.det_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed

