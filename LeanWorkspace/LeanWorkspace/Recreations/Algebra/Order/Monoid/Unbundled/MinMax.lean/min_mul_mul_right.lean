import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

variable [MulRightMono α]

theorem min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c := (monotone_id.mul_const' c).map_min.symm

