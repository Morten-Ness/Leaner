import Mathlib

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_mul x, CharTwo.two_eq_zero, zero_mul]

