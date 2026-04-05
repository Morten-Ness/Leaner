import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem lt_mul_of_lt_of_one_lt [MulLeftStrictMono α] {a b c : α} (hbc : b < c)
    (ha : 1 < a) :
    b < c * a := calc
    b < c := hbc
    _ = c * 1 := (mul_one c).symm
    _ < c * a := mul_lt_mul_right ha c

