import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.mul_lt_one_of_le_of_lt [MulRightMono α] {a b : α}
    (ha : a ≤ 1) (hb : b < 1) :
    a * b < 1 := mul_lt_of_le_one_of_lt ha hb

