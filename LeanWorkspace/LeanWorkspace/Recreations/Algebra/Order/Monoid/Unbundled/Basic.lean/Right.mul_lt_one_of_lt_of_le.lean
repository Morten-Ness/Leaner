import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.mul_lt_one_of_lt_of_le [MulRightStrictMono α] {a b : α}
    (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := mul_lt_of_lt_one_of_le ha hb

