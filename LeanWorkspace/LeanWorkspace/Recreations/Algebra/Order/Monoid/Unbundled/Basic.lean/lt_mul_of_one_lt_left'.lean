import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_mul_of_one_lt_left' [MulRightStrictMono α] (a : α) {b : α}
    (h : 1 < b) :
    a < b * a := calc
    a = 1 * a := (one_mul a).symm
    _ < b * a := mul_lt_mul_left h a

