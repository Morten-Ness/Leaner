import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_mul_of_lt_of_one_lt' [MulLeftMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a := lt_mul_of_lt_of_one_le hbc ha.le

