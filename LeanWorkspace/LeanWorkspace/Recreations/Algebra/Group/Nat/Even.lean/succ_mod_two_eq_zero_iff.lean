import Mathlib

variable {m n : ℕ}

theorem succ_mod_two_eq_zero_iff : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by lia

