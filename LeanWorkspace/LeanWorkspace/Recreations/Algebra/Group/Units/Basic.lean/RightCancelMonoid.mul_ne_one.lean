import Mathlib

variable {α : Type u}

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

