import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_pow (M : Matrix m m R) (n : ℕ) : Matrix.det (M ^ n) = Matrix.det M ^ n := (Matrix.detMonoidHom : Matrix m m R →* R).map_pow M n

