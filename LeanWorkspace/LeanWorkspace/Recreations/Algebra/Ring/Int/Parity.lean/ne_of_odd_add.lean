import Mathlib

variable {m n : ℤ}

theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind

