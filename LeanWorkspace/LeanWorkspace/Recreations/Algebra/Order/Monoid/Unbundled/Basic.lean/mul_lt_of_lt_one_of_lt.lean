import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [Preorder α]

theorem mul_lt_of_lt_one_of_lt [MulRightStrictMono α] {a b c : α} (ha : a < 1)
    (hb : b < c) :
    a * b < c := calc
    a * b < 1 * b := mul_lt_mul_left ha b
    _ = b := one_mul b
    _ < c := hb

