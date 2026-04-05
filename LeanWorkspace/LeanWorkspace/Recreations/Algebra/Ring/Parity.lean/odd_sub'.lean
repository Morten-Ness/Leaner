import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem odd_sub' (h : n ≤ m) : Odd (m - n) ↔ (Odd n ↔ Even m) := by grind

