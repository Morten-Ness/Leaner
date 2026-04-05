import Mathlib

variable {m n : ℕ}

theorem succ_mod_two_eq_one_iff : (m + 1) % 2 = 1 ↔ m % 2 = 0 := by lia

