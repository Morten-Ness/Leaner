import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h

