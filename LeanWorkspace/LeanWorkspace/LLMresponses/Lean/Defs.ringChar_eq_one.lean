FAIL
import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  constructor
  · intro h
    rw [subsingleton_iff]
    intro a b
    have h1 : (1 : R) = 0 := by
      exact (ringChar.spec R 1).mp h
    calc
      a = a + 0 := by rw [add_zero]
      _ = a + 1 := by rw [h1]
      _ = a + (1 * b) := by rw [one_mul]
      _ = a + (1 • b) := by rw [one_nsmul]
      _ = a + b := by simp
      _ = b + a := by rw [add_comm]
      _ = (1 • a) + b := by rw [one_nsmul]
      _ = (1 * a) + b := by rw [one_mul]
      _ = 1 + b := by rw [h1]
      _ = 0 + b := by rw [h1]
      _ = b := by rw [zero_add]
  · intro h
    have h1 : (1 : R) = 0 := Subsingleton.elim _ _
    exact (ringChar.spec R 1).mpr h1
