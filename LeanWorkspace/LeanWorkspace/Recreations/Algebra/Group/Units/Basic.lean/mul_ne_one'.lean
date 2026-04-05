import Mathlib

variable {α : Type u}

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem mul_ne_one' : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := LeftCancelMonoid.mul_ne_one

