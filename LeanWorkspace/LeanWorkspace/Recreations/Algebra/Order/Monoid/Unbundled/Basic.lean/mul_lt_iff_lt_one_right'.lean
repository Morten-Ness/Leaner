import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem mul_lt_iff_lt_one_right' [MulRightStrictMono α]
    [MulRightReflectLT α] {a : α} (b : α) : a * b < b ↔ a < 1 := Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_right b)

