import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem even_two_mul (a : α) : Even (2 * a) := ⟨a, two_mul _⟩

