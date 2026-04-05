import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact mod_cast h

