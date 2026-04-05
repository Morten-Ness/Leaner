import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_lt_of_lt_one_of_lt' [MulRightMono α] {a b c : α} (ha : a < 1)
    (hbc : b < c) :
    a * b < c := mul_lt_of_le_one_of_lt ha.le hbc

