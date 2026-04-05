import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_mul_of_one_lt_of_lt' [MulRightMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c := lt_mul_of_one_le_of_lt ha.le hbc

