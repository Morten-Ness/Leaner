FAIL
import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  intro h
  letI : CharZero R := ringChar.eq_zero_of_one_eq_zero (R := R) (by simpa using h)
  exact CharZero.nontrivial_iff_two_ne_zero.mp inferInstance (by simp)
