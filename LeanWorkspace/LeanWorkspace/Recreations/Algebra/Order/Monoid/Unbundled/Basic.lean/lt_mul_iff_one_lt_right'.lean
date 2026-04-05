import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_mul_iff_one_lt_right' [MulLeftStrictMono α]
    [MulLeftReflectLT α] (a : α) {b : α} :
    a < a * b ↔ 1 < b := Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

