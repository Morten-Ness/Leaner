import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_mul_of_one_le_right' [MulLeftMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ a * b := calc
    a = a * 1 := (mul_one a).symm
    _ ≤ a * b := mul_le_mul_right h a

