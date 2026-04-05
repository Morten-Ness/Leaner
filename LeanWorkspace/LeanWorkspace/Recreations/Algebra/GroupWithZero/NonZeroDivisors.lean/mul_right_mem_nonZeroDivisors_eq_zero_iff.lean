import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem mul_right_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : x * r = 0 ↔ x = 0 := mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hr.2

