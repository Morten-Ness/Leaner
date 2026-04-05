import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_mul_comm (M N : Matrix m m R) : Matrix.det (M * N) = Matrix.det (N * M) := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm]

