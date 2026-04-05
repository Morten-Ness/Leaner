import Mathlib

variable {S M G : Type*}

variable [MulOneClass M]

theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]

