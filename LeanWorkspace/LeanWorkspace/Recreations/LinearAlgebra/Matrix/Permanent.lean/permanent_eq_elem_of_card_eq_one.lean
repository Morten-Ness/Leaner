import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_eq_elem_of_card_eq_one {A : Matrix n n R} (h : card n = 1) (k : n) :
    Matrix.permanent A = A k k := haveI : Subsingleton n := card_le_one_iff_subsingleton.mp h.le
  Matrix.permanent_eq_elem_of_subsingleton _ _

