import Mathlib

variable {α : Type u}

variable [RightCancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [RightCancelMonoid.eq_one_of_mul_right h, one_mul] at h

