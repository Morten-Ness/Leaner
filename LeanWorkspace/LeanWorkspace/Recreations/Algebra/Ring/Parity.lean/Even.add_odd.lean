import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Even.add_odd : Even a → Odd b → Odd (a + b) := by
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, by rw [mul_add, ← two_mul, add_assoc]⟩

