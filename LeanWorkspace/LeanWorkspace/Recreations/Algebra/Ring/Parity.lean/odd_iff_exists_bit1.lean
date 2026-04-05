import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem odd_iff_exists_bit1 : Odd a ↔ ∃ b, a = 2 * b + 1 := exists_congr fun b ↦ by rw [two_mul]

alias ⟨Odd.exists_bit1, _⟩ := odd_iff_exists_bit1

