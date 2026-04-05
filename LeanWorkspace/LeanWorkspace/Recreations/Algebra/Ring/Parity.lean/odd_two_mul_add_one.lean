import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem odd_two_mul_add_one (a : α) : Odd (2 * a + 1) := ⟨_, rfl⟩

