import Mathlib

variable {α : Type u}

variable [Group α] [LinearOrder α]

theorem cmp_div_one' [MulRightMono α] (a b : α) :
    cmp (a / b) 1 = cmp a b := by rw [← cmp_mul_right' _ _ b, one_mul, div_mul_cancel]

