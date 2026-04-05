import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_zero_of_row_eq_zero {A : Matrix n n R} (i : n) (h : ∀ j, A i j = 0) : Matrix.det A = 0 := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_coord_zero i (funext h)

