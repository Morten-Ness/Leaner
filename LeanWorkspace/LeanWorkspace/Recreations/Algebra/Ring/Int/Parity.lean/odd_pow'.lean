import Mathlib

variable {m n : ℤ}

theorem odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m := by grind

