import Mathlib

variable (R : Type*)

theorem Ring.neg_one_ne_one_of_char_ne_two {R : Type*} [NonAssocRing R] [Nontrivial R]
    (hR : ringChar R ≠ 2) : (-1 : R) ≠ 1 := fun h =>
  Ring.two_ne_zero hR (one_add_one_eq_two (R := R) ▸ neg_eq_iff_add_eq_zero.mp h)

