import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by grind

