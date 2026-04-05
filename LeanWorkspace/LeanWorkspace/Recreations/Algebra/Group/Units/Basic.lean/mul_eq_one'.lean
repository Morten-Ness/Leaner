import Mathlib

variable {α : Type u}

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem mul_eq_one' : a * b = 1 ↔ a = 1 ∧ b = 1 := LeftCancelMonoid.mul_eq_one

