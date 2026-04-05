import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_div : Even (m / n) ↔ m % (2 * n) / n = 0 := by
  rw [even_iff_two_dvd, dvd_iff_mod_eq_zero, ← Nat.mod_mul_right_div_self, mul_comm]

