import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem Left.mul_lt_one [MulLeftStrictMono α] {a b : α} (ha : a < 1) (hb : b < 1) :
    a * b < 1 := mul_lt_of_lt_of_lt_one ha hb

