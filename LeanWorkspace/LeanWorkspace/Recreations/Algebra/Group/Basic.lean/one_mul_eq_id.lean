import Mathlib

variable {α β G M : Type*}

variable [MulOneClass M]

theorem one_mul_eq_id : ((1 : M) * ·) = id := funext one_mul

