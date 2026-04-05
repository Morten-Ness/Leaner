import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_eq_one_of_card_eq_zero {A : Matrix n n R} (h : card n = 0) : Matrix.permanent A = 1 := haveI : IsEmpty n := card_eq_zero_iff.mp h
  Matrix.permanent_isEmpty

