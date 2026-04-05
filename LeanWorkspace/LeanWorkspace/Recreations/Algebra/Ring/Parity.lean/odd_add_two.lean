import Mathlib

variable {F α β : Type*}

variable [Ring α] {a b : α} {n : ℕ}

theorem odd_add_two : Odd (a + 2) ↔ Odd a := by
  rw [← one_add_one_eq_two, ← add_assoc, odd_add_one, even_add_one]

