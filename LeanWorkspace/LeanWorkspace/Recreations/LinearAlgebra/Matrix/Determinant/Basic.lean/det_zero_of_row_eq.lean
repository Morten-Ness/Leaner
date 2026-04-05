import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {M : Matrix n n R} {i j : n}

theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_eq_zero_of_eq M hij i_ne_j

