import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by grind

