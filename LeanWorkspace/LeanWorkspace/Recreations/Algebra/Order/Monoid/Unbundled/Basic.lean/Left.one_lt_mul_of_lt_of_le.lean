import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Left.one_lt_mul_of_lt_of_le [MulLeftMono α] {a b : α} (ha : 1 < a)
    (hb : 1 ≤ b) :
    1 < a * b := lt_mul_of_lt_of_one_le ha hb

