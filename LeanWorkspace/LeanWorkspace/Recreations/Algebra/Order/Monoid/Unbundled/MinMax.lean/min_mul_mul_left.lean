import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

variable [MulLeftMono α]

theorem min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c := (monotone_id.const_mul' a).map_min.symm

