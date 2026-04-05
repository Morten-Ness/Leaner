import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

variable [MulRightMono α]

theorem max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c := (monotone_id.mul_const' c).map_max.symm

