import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_eq_one_of_card_eq_one {A : Matrix n n α} (h : Fintype.card n = 1) :
    Matrix.adjugate A = 1 := haveI : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp h.le
  Matrix.adjugate_subsingleton _

