import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem isUnit_of_left_inverse (h : B * A = 1) : IsUnit A := .of_mul_eq_one_right _ h

