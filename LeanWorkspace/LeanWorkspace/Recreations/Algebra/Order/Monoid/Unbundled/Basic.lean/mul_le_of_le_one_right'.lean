import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem mul_le_of_le_one_right' [MulLeftMono α] {a b : α} (h : b ≤ 1) :
    a * b ≤ a := calc
    a * b ≤ a * 1 := mul_le_mul_right h a
    _ = a := mul_one a

