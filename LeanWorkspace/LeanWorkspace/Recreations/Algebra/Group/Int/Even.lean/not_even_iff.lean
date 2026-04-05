import Mathlib

variable {m n : ℤ}

theorem not_even_iff : ¬Even n ↔ n % 2 = 1 := by grind

