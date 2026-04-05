import Mathlib

variable {m n : ℕ}

theorem one_lt_of_ne_zero_of_even (h0 : n ≠ 0) (hn : Even n) : 1 < n := by grind

