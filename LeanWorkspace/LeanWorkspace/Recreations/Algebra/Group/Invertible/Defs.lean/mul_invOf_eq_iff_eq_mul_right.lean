import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c), invOf_mul_cancel_right]

