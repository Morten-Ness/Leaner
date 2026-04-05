import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), invOf_mul_cancel_left]

