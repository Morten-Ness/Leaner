import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  rw [← Nat.dvd_one, ← ringChar.spec, eq_comm, Nat.cast_one, subsingleton_iff_zero_eq_one]

