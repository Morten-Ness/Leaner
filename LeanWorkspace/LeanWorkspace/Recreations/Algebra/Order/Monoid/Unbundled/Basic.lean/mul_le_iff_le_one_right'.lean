import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem mul_le_iff_le_one_right' [MulLeftMono α]
    [MulLeftReflectLE α] (a : α) {b : α} :
    a * b ≤ a ↔ b ≤ 1 := Iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

