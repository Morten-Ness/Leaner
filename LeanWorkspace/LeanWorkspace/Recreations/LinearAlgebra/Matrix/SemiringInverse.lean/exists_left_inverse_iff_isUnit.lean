import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem exists_left_inverse_iff_isUnit : (∃ B, B * A = 1) ↔ IsUnit A := isUnit_iff_exists_inv'.symm

