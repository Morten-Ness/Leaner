import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [Preorder α]

theorem mul_le_of_mul_le_right [MulRightMono α] {a b c d : α}
    (h : a * b ≤ c) (hle : d ≤ a) :
    d * b ≤ c := (mul_le_mul_left hle b).trans h

