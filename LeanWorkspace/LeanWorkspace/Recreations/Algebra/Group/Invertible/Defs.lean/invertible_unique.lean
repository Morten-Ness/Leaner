import Mathlib

variable {α : Type u}

variable [Monoid α] (a b : α)

theorem invertible_unique [Invertible a] [Invertible b]
    (h : a = b) : ⅟a = ⅟b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]

