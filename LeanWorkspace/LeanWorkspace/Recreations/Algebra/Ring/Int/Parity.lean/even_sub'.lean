import Mathlib

variable {m n : ℤ}

theorem even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

