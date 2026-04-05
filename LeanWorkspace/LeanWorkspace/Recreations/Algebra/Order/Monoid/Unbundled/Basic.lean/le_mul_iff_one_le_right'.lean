import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_mul_iff_one_le_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a ≤ a * b ↔ 1 ≤ b := Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

