import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem mul_lt_of_lt_one_right' [MulLeftStrictMono α] (a : α) {b : α} (h : b < 1) :
    a * b < a := calc
    a * b < a * 1 := mul_lt_mul_right h a
    _ = a := mul_one a

