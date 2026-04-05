import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem detp_neg_one_one : Matrix.detp (-1) (1 : Matrix n n R) = 0 := by
  rw [← diagonal_one, Matrix.detp_neg_one_diagonal]

