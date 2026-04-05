import Mathlib

variable {α β : Type*}

variable [MulOneClass α]

variable [LT α]

theorem one_lt_of_lt_mul_left [MulRightReflectLT α] {a b : α}
    (h : b < a * b) :
    1 < a := lt_of_mul_lt_mul_right' (a := b) <| by simpa only [one_mul]

