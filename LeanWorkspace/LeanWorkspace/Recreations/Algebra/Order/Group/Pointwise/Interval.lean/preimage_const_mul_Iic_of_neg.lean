import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using Set.preimage_mul_const_Iic_of_neg a h

