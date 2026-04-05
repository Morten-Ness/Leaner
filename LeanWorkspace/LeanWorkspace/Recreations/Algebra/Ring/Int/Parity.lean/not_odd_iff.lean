import Mathlib

variable {m n : ℤ}

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

