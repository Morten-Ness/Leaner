import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem min_mul [MulRightMono α] (a b c : α) :
    min a b * c = min (a * c) (b * c) := mul_left_mono.map_min

