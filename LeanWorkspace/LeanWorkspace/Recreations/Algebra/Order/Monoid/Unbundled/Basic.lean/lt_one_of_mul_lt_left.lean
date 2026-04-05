import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem lt_one_of_mul_lt_left [MulRightReflectLT α] {a b : α}
    (h : a * b < b) :
    a < 1 := lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

