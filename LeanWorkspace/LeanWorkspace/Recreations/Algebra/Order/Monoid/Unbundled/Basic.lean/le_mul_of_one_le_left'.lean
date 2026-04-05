import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem le_mul_of_one_le_left' [MulRightMono α] {a b : α} (h : 1 ≤ b) :
    a ≤ b * a := calc
    a = 1 * a := (one_mul a).symm
    _ ≤ b * a := mul_le_mul_left h a

