import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem one_le_of_le_mul_right [MulLeftReflectLE α] {a b : α} (h : a ≤ a * b) :
    1 ≤ b := le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

