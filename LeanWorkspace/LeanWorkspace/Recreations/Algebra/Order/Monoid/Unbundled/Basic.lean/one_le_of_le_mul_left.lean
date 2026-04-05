import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem one_le_of_le_mul_left [MulRightReflectLE α] {a b : α}
    (h : b ≤ a * b) :
    1 ≤ a := le_of_mul_le_mul_right' (a := b) <| by simpa only [one_mul]

