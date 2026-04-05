import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem mul_lt_iff_lt_one_left' [MulLeftStrictMono α]
    [MulLeftReflectLT α] {a b : α} :
    a * b < a ↔ b < 1 := Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_left a)

