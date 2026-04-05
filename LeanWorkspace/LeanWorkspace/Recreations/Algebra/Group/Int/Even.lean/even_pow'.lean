import Mathlib

variable {m n : ℤ}

theorem even_pow' {n : ℕ} (h : n ≠ 0) : Even (m ^ n) ↔ Even m := by grind

