import Mathlib

variable {m n : ℤ}

theorem coe_nat_two_pow_pred (p : ℕ) : ((2 ^ p - 1 : ℕ) : ℤ) = (2 ^ p - 1 : ℤ) := Int.natCast_pow_pred 2 p (by decide)

