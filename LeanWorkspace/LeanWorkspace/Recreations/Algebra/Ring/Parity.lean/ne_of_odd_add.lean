import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by grind

