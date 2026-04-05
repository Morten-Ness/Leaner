import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_xor_odd (n : ℕ) : Xor' (Even n) (Odd n) := by grind

