import Mathlib

variable {α : Type u}

variable [LeftCancelMonoid α] [Subsingleton αˣ] {a b : α}

theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 := congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by
    rw [← mul_left_cancel_iff (a := a), ← mul_assoc, h, one_mul, mul_one]) h) 1

