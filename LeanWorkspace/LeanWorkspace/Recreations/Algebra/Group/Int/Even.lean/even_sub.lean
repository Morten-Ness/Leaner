import Mathlib

variable {m n : ℤ}

theorem even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by grind

