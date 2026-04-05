import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Right.one_lt_mul [MulRightStrictMono α] {a b : α} (ha : 1 < a)
    (hb : 1 < b) :
    1 < a * b := lt_mul_of_one_lt_of_lt ha hb

