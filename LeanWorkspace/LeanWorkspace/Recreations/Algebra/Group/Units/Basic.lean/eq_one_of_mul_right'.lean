import Mathlib

variable {α : Type u}

variable [CancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem eq_one_of_mul_right' (h : a * b = 1) : a = 1 := LeftCancelMonoid.eq_one_of_mul_right h

