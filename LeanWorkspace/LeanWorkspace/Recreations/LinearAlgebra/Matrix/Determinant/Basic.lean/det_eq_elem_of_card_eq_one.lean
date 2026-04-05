import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_elem_of_card_eq_one {A : Matrix n n R} (h : Fintype.card n = 1) (k : n) :
    Matrix.det A = A k k := haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  Matrix.det_eq_elem_of_subsingleton _ _

