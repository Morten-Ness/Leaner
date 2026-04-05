import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_mul_of_one_lt_right' [MulLeftStrictMono α] (a : α) {b : α} (h : 1 < b) :
    a < a * b := calc
    a = a * 1 := (mul_one a).symm
    _ < a * b := mul_lt_mul_right h a

