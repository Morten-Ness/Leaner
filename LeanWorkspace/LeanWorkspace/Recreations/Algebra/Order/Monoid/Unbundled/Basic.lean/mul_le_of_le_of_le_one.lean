import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_le_of_le_of_le_one [MulLeftMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a ≤ 1) :
    b * a ≤ c := calc
    b * a ≤ b * 1 := mul_le_mul_right ha b
    _ = b := mul_one b
    _ ≤ c := hbc

