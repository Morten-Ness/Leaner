import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem one_lt_of_lt_mul_right [MulLeftReflectLT α] {a b : α} (h : a < a * b) :
    1 < b := lt_of_mul_lt_mul_left' (a := a) <| by simpa only [mul_one]

