import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem eq_zero_of_ne_zero_of_mul_right_eq_zero (hx : x ≠ 0) (hxy : y * x = 0) : y = 0 := Or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hxy) hx

