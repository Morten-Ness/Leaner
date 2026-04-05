import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_sub' (h : n ≤ m) : Even (m - n) ↔ (Odd m ↔ Odd n) := by grind

