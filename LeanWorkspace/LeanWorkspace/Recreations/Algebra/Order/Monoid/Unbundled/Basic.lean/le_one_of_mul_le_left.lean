import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_one_of_mul_le_left [MulRightReflectLE α] {a b : α}
    (h : a * b ≤ b) :
    a ≤ 1 := le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

