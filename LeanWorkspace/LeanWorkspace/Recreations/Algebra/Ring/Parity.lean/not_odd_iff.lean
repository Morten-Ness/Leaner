import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by grind

