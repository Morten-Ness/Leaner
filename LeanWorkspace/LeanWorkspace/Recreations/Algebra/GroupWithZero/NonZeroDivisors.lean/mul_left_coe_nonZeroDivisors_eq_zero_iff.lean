import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_left_coe_nonZeroDivisors_eq_zero_iff {c : M₀⁰} : (c : M₀) * x = 0 ↔ x = 0 := mul_left_mem_nonZeroDivisors_eq_zero_iff c.prop

