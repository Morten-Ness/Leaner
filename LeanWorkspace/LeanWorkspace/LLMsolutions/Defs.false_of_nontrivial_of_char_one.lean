FAIL
import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  exact CharZero.ne_zero (R := R) 1 (by decide) (CharP.cast_eq_zero (R := R) (p := 1))
