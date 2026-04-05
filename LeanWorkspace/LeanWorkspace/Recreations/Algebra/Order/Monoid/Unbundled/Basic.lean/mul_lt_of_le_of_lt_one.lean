import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_lt_of_le_of_lt_one [MulLeftStrictMono α] {a b c : α} (hbc : b ≤ c)
    (ha : a < 1) :
    b * a < c := calc
    b * a < b * 1 := mul_lt_mul_right ha b
    _ = b := mul_one b
    _ ≤ c := hbc

