import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem mul_le_iff_le_one_left' [MulRightMono α]
    [MulRightReflectLE α] {a b : α} :
    a * b ≤ b ↔ a ≤ 1 := Iff.trans (by rw [one_mul]) (mul_le_mul_iff_right b)

