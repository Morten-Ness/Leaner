import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem isUnit_of_right_inverse (h : A * B = 1) : IsUnit A := .of_mul_eq_one _ h

