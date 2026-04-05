import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_one_of_card_eq_zero {A : Matrix n n R} (h : Fintype.card n = 0) : Matrix.det A = 1 := haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h
  Matrix.det_isEmpty

