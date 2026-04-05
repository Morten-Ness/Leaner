import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_mul_iff_one_lt_left' [MulRightStrictMono α]
    [MulRightReflectLT α] (a : α) {b : α} : a < b * a ↔ 1 < b := Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right a)

