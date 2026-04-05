import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using Set.preimage_mul_const_Ioi_of_neg a h

