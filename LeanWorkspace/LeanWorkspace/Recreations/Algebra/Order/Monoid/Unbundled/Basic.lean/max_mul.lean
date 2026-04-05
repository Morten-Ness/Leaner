import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem max_mul [MulRightMono α] (a b c : α) :
    max a b * c = max (a * c) (b * c) := mul_left_mono.map_max

