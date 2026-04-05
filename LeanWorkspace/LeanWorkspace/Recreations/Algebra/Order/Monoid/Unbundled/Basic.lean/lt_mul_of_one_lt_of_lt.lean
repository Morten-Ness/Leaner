import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_mul_of_one_lt_of_lt [MulRightStrictMono α] {a b c : α} (ha : 1 < a)
    (hbc : b < c) :
    b < a * c := calc
    b < c := hbc
    _ = 1 * c := (one_mul c).symm
    _ < a * c := mul_lt_mul_left ha c

