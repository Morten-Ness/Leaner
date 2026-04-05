import Mathlib

variable {m n : ℤ}

theorem odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

