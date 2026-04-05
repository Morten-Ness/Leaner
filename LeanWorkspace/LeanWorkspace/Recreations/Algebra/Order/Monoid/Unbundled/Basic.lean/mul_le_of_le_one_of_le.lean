import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_le_of_le_one_of_le [MulRightMono α] {a b c : α} (ha : a ≤ 1)
    (hbc : b ≤ c) :
    a * b ≤ c := calc
    a * b ≤ 1 * b := mul_le_mul_left ha b
    _ = b := one_mul b
    _ ≤ c := hbc

