import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_zero (_ : Nonempty n) : Matrix.det (0 : Matrix n n R) = 0 := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_zero

