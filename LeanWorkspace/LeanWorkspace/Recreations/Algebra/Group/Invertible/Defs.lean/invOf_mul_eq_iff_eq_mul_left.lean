import Mathlib

variable {α : Type u}

variable [Monoid α] {a b c : α} [Invertible c]

theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_cancel_left]

