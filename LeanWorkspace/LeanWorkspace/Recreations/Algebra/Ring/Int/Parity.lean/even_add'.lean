import Mathlib

variable {m n : ℤ}

theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

