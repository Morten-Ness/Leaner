import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.toLin'_mul_apply [Fintype m] [DecidableEq m] (M : Matrix l m R) (N : Matrix m n R)
    (x) : Matrix.toLin' (M * N) x = Matrix.toLin' M (Matrix.toLin' N x) := by
  rw [Matrix.toLin'_mul, LinearMap.comp_apply]

