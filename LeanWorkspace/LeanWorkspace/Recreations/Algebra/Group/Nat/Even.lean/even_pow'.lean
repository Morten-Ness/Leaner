import Mathlib

variable {m n : ℕ}

theorem even_pow' (h : n ≠ 0) : Even (m ^ n) ↔ Even m := by grind

