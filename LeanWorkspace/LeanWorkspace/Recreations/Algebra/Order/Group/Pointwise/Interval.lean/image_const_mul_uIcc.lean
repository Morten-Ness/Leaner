import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem image_const_mul_uIcc (a b c : α) : (a * ·) '' [[b, c]] = [[a * b, a * c]] := by
  simpa only [mul_comm] using Set.image_mul_const_uIcc a b c

