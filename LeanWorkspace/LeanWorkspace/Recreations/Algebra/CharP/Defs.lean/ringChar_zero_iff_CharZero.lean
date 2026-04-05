import Mathlib

variable (R : Type*)

variable [NonAssocRing R]

theorem ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff ringChar, CharP.charP_zero_iff_charZero]

