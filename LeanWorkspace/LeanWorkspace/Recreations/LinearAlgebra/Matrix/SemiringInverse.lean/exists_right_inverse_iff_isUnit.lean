import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem exists_right_inverse_iff_isUnit : (∃ B, A * B = 1) ↔ IsUnit A := isUnit_iff_exists_inv.symm

