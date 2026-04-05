import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_one_of_mul_lt_right [MulLeftReflectLT α] {a b : α} (h : a * b < a) :
    b < 1 := lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

