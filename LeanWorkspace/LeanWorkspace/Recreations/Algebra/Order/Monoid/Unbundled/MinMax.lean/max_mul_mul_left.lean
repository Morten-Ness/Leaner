import Mathlib

variable {α β : Type*}

variable [LinearOrder α]

variable [Mul α]

variable [MulLeftMono α]

theorem max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c := (monotone_id.const_mul' a).map_max.symm

