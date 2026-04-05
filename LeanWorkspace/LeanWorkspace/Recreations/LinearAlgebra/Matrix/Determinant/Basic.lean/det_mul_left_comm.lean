import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul_left_comm (M N P : Matrix m m R) : Matrix.det (M * (N * P)) = Matrix.det (N * (M * P)) := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.det_mul, Matrix.det_mul_comm M N, ← Matrix.det_mul]

