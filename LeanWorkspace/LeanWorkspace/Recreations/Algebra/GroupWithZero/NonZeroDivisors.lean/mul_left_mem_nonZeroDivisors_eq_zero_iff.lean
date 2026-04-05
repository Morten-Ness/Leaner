import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_left_mem_nonZeroDivisors_eq_zero_iff (hr : r ∈ M₀⁰) : r * x = 0 ↔ x = 0 := by
  rw [mul_comm, mul_right_mem_nonZeroDivisors_eq_zero_iff hr]

