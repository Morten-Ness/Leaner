import Mathlib

variable {m n : ℤ}

theorem odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by grind

