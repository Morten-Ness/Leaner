import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), mul_invOf_cancel_right]

