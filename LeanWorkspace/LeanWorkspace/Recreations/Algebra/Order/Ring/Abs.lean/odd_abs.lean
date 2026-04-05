import Mathlib

variable {α : Type*}

theorem odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a := by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

