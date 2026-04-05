import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem mul_lt_of_lt_one_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : b < 1) :
    b * a < a := calc
    b * a < 1 * a := mul_lt_mul_left h a
    _ = a := one_mul a

