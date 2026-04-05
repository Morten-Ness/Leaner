import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem odd_add_one {n : ℕ} : Odd (n + 1) ↔ ¬ Odd n := by grind

