import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LE α]

theorem mul_le_of_le_one_left' [MulRightMono α] {a b : α} (h : b ≤ 1) :
    b * a ≤ a := calc
    b * a ≤ 1 * a := mul_le_mul_left h a
    _ = a := one_mul a

