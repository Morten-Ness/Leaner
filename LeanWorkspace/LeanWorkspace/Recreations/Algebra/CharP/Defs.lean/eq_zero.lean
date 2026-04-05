import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem eq_zero [CharZero R] : ringChar R = 0 := ringChar.eq R 0

