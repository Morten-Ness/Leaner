import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using Set.preimage_mul_const_Ico_of_neg a b h

