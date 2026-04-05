import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using Set.preimage_mul_const_Ioc_of_neg a b h

