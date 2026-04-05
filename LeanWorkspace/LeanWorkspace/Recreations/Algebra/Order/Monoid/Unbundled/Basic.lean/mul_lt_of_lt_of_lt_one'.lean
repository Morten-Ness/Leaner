import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_lt_of_lt_of_lt_one' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : a < 1) :
    b * a < c := mul_lt_of_lt_of_le_one hbc ha.le

