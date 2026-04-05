import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_one_of_mul_le_right [MulLeftReflectLE α] {a b : α} (h : a * b ≤ a) :
    b ≤ 1 := le_of_mul_le_mul_left' (a := a) <| by simpa only [mul_one]

