import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_mul_iff_one_le_left' [MulRightMono α]
    [MulRightReflectLE α] (a : α) {b : α} :
    a ≤ b * a ↔ 1 ≤ b := Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right a)

