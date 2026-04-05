import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem even_iff_exists_two_mul : Even a ↔ ∃ b, a = 2 * b := by simp [even_iff_exists_two_nsmul]

