import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem odd_pow_iff {e : ℕ} (he : e ≠ 0) : Odd (n ^ e) ↔ Odd n := by grind

